#!/usr/bin/env python3
"""ntru: a new hope"""

import secrets
import hashlib
import random
import re
import math
import sys

def extended_euclidean_algorithm(a, b):
    """purely iterative version of the extended euclidean algorithm.
       compute gcd of integers a and b, as well as integers x and y"""
    """ such that ax + by = gcd(x,y). return (x,y,gcd(a,b))."""
    assert type(a) is int and type(b) is int

    sign_a = 1
    sign_b = 1

    if a < 0:
        sign_a = -1
        a = -a
    if b < 0:
        sign_b = -1
        b = -b

    # maintain the loop invariant: r_j = s_j * a + t_j * b, for all j > 0
    r_j_2 = a; s_j_2 = 1; t_j_2 = 0
    r_j_1 = b; s_j_1 = 0; t_j_1 = 1

    while r_j_1 > 0:
        q_j_1 = r_j_2 // r_j_1
        
        r_j = r_j_2 - q_j_1 * r_j_1
        s_j = s_j_2 - q_j_1 * s_j_1
        t_j = t_j_2 - q_j_1 * t_j_1

        r_j_1, r_j_2 = r_j, r_j_1
        s_j_1, s_j_2 = s_j, s_j_1
        t_j_1, t_j_2 = t_j, t_j_1

    return (sign_a * s_j_2, sign_b * t_j_2, r_j_2)


def mod_inverse(num, m):
    """calculate multiplicative inverse of num, modulo a positive integer m"""
    assert(m > 0)

    a, b, g = extended_euclidean_algorithm(num, m)

    if g != 1:
        raise ArithmeticError('the number %d does not have a multiplicative inverse modulo %d'
                         % (num, m))
    return a % m



def str2coefflist(s):
    """convert a string representation of a polynomial to a list of coefficients."""
    """ last element of the list (highest degree term) is non zero. the zero polynomial"""
    """ is represented by an empty list."""
    coefflist = []
    degree = -1
    s = s.replace('-', '+-')
    terms = s.split('+')
    for term in terms:
        term = term.replace(' ', '')
        match = re.fullmatch(r"""(?xi)
                                 (-?\d+)? (?# group 1: coefficient for this term)
                                 (\*? x (?: (?:\^|\*\*) (?# group 2: is there an x?)
                                            (\d+) (?# group 3: exponent)
                                        )?)?""",
                             term)
        if match is None: # match failed
            raise SyntaxError('polynomial must be a sum of terms k*x^e')
        coeff, xterm, exponent = match.groups()
        if coeff is None and xterm is None:
            continue
        coeff = 1 if coeff is None else int(coeff)
        if exponent is None and xterm is None:
            exponent = 0
        elif exponent is None:
            exponent = 1
        else:
            exponent = int(exponent)
        
        if coeff != 0:
            for i in range(degree + 1, exponent + 1):
                coefflist.append(0)
                degree += 1
            coefflist[exponent] += coeff

    return coefflist


def coefflist2str(coefflist):
    """convert a coefficient list of a polynomial to a string representation"""
    noitems = True
    s = ''
    for i in range(len(coefflist) - 1, -1, -1):
        if coefflist[i] != 0:
            if coefflist[i] > 0:
                if noitems == False:
                    sign = '+'
                else:
                    sign = ''
            else:
                sign = '-'
            if abs(coefflist[i]) != 1 or i == 0:
                coeff = ' ' + str(abs(coefflist[i]))
            else:
                coeff = ''
            if i > 0:
                x = ' x'
            else:
                x = ''
            if i > 1:
                exponent = '^%d' % i
            else:
                exponent = ''
            s += ' %s%s%s%s' % (sign, coeff, x, exponent)
            noitems = False
    if noitems == True:
        s = '0'
    return s.strip()



class conv_poly():
    """represents polynomials in the ring Z[x]/(x^n - 1) or Z/pZ[x]/(x^n - 1)
       invariant: coefficients in [0, self.coeff_mod) if self.coeff_mod is not None. otherwise there is no restriction.
       degree is maintained as the highest non-zero term or -1 if equal to the zero polynomial"""
    def __init__(self, n, p=None, polynomial=None):
        self.coefflist = [0] * (n + 1) # zero polynomial with n coefficients, going from a_0, ..., a_{n - 1} (but we leave space for an extra coefficient)
        self.n = n
        self.coeff_mod = p # polynomial in Z[x]/(x^n - 1) ring by default
        self.degree = -1 # zero polynomial
        if polynomial is not None:
            lst = str2coefflist(polynomial)
            for i, c in enumerate(lst):
                self.coefflist[i] = c
                if p is not None:
                    self.coefflist[i] %= p
                if self.coefflist[i] != 0:
                    self.degree = i


    def __str__(self):
        return coefflist2str(self.coefflist)

    def __repr__(self):
        return 'conv_poly(polynomial=%s, n=%d, p=%s)' % (self.__str__(), self.n, str(self.coeff_mod))

    def leading_coeff(self):
        if self.degree == -1:
            return 0
        else:
            return self.coefflist[self.degree]

    def get_degree(self):
        for i in range(len(self.coefflist) - 1, -1, -1):
            if self.coefflist[i] != 0:
                return i
        return -1

    def set_coeff_mod(self, coeff_mod):
        """!!mutates!! the polynomial by taking every coefficient modulo a new value and changing the modulus of the polynomial"""
        self.coeff_mod = coeff_mod
        for i in range(len(self.coefflist)):
            self.coefflist[i] %= coeff_mod
        self.degree = self.get_degree()

    def lift(self):
        """!!mutates!! the polynomial and """
        """provides a way of mapping polynomials 
           from Z/pZ[x]/(x^n - 1) to Z[x]/(x^n - 1) that is used in ntru"""
        if self.coeff_mod == None:
            raise Exception('polynomial already belongs to the Z[x]/(x^n - 1) ring')
        for i in range(0, self.degree + 1):
            if self.coefflist[i] > self.coeff_mod // 2:
                self.coefflist[i] -= self.coeff_mod
        self.coeff_mod = None

    def copy(self, new_coeff_mod=None):
        """if new_coeff_mod is not None, the modulus for the new polynomial given by this parameter""" 
        new_poly = conv_poly(self.n, self.coeff_mod)
        new_poly.coefflist = self.coefflist.copy()
        new_poly.degree = self.degree

        if new_coeff_mod is not None and new_coeff_mod != self.coeff_mod:
            new_poly.set_coeff_mod(new_coeff_mod)
        return new_poly

    def __eq__(self, other):
        if self.degree != other.degree:
            return False
        for i in range(self.degree, -1, -1):
            if self.coefflist[i] != other.coefflist[i]:
                return False
        return True

    def __ne__(self, other):
        return not self.__eq__(other)


    def __add__(self, other, op='add'):
        """creates a new polynomial that is the sum or difference of the two operands"""
        sign = 1 if op == 'add' else -1
        assert (self.coeff_mod == other.coeff_mod)
        new_poly = conv_poly(self.n, self.coeff_mod)
        i = 0
        while i <= self.degree or i <= other.degree:
            new_poly.coefflist[i] = self.coefflist[i] + sign * other.coefflist[i]
            if new_poly.coeff_mod is not None:
                new_poly.coefflist[i] %= new_poly.coeff_mod
            if new_poly.coefflist[i] != 0:
                new_poly.degree = i
            i += 1
        return new_poly

    def __sub__(self, other):
        """creates a new polynomial that is the difference of the two operands"""
        return self.__add__(other, 'sub')

    def __mul__(self, other):
        """creates a new polynomial that is the product of the two operands"""
        assert self.coeff_mod == other.coeff_mod and self.n == other.n
        new_poly = conv_poly(self.n, self.coeff_mod)
        for i in range(self.n):
            for j in range(self.n):
                new_poly.coefflist[i] += self.coefflist[j] * other.coefflist[(i - j) % self.n]
            if new_poly.coeff_mod is not None:
                new_poly.coefflist[i] %= new_poly.coeff_mod
            if new_poly.coefflist[i] != 0:
                new_poly.degree = i
        return new_poly

    def mult_by_term(self, coeff, power):
        """this operation multiplies a polynomial by coeff * x^power (a new polynomial is returned).
           it assumes that self.degree + power <= self.n, so there is space is the coefflist"""

        new_poly = conv_poly(self.n, self.coeff_mod)
        for i in range(self.degree, -1, -1):
            new_poly.coefflist[power + i] = coeff * self.coefflist[i]
            if new_poly.coeff_mod is not None:
                new_poly.coefflist[power + i] %= new_poly.coeff_mod

        new_poly.degree = new_poly.get_degree()
        return new_poly

    def make_monic(self):
        """returns a new non-zero polynomial that is monic by dividing through by the leading coefficient"""

        if self.degree == -1: # zero polynomial cannot be monic
            raise ValueError('tried to make the zero polynomial monic, which is not possible')
        else:
            return self.mult_by_term(coeff=mod_inverse(self.leading_coeff(), self.coeff_mod), power=0)


    def poly_extended_euclidean_algorithm(self, b):
        """iterative version of the extended euclidean algorithm for polynomials
           takes 2 polynomials with coefficients in Z_p and returns a gcd for them, as well
           as polynomials x and y such that ax + by = gcd"""

        a = self
        assert a.coeff_mod is not None and a.coeff_mod == b.coeff_mod and a.n == b.n

        p = a.coeff_mod
        zero_poly = conv_poly(self.n, p=p)
        one_poly = conv_poly(self.n, p=p)
        one_poly.coefflist[0] = 1
        one_poly.degree = 0

        # maintain the loop invariant: r_j = s_j * a + t_j * b, for all j > 0
        r_j_2 = a; s_j_2 = one_poly; t_j_2 = zero_poly
        r_j_1 = b; s_j_1 = zero_poly; t_j_1 = one_poly

        while r_j_1.degree != -1: # while r_j_1 is not the zero polynomial
            if r_j_2.degree < r_j_1.degree:
                # must switch the two
                r_j_1, r_j_2 = r_j_2, r_j_1
                s_j_1, s_j_2 = s_j_2, s_j_1
                t_j_1, t_j_2 = t_j_2, t_j_1
                continue

            # must compute r_j = r_j_2 - a_n * b_k_inv * x^(n - k) * r_j_1
            b_k_inv =  mod_inverse(r_j_1.leading_coeff(), p)
            a_n = r_j_2.leading_coeff()
            n_minus_k = r_j_2.degree - r_j_1.degree

            r_j = r_j_2 - r_j_1.mult_by_term(coeff=((b_k_inv * a_n) % p), power=n_minus_k)
            s_j = s_j_2 - s_j_1.mult_by_term(coeff=((b_k_inv * a_n) % p), power=n_minus_k)
            t_j = t_j_2 - t_j_1.mult_by_term(coeff=((b_k_inv * a_n) % p), power=n_minus_k)

            r_j_1, r_j_2 = r_j, r_j_1
            s_j_1, s_j_2 = s_j, s_j_1
            t_j_1, t_j_2 = t_j, t_j_1

        return (s_j_2, t_j_2, r_j_2)

    def invert_with_prime_mod_coeffs(self):
        """designed for polynomials with coefficients in Z_p, p prime"""
        assert self.coeff_mod is not None

        mod_poly = conv_poly(self.n, self.coeff_mod)
        mod_poly.coefflist[self.n] = 1
        mod_poly.coefflist[0] = self.coeff_mod - 1
        mod_poly.degree = self.n

        x, y, g = self.poly_extended_euclidean_algorithm(mod_poly)
        if g.degree != 0: # if not a constant, non-zero polynomial, the polynomial is not invertible
            raise ArithmeticError('the polynomial does not have a multiplicative inverse modulo')

        x_adjusted = x.mult_by_term(coeff=mod_inverse(g.leading_coeff(), self.coeff_mod), power=0)
        if x_adjusted.coefflist[self.n] != 0:
            x_adjusted.coefflist[0] = (x_adjusted.coefflist[0] + x_adjusted.coefflist[self.n]) % self.coeff_mod
            x_adjusted.coefflist[self.n] = 0
            x_adjusted.degree = x_adjusted.get_degree()

        return x_adjusted

    def invert_with_prime_power_mod_coeffs(self, q=None, p=None):
        """invert a polynomial in (Z/qZ[x] / x^n - 1), where q = p^k, p being a prime"""
        if q is None:
            q = self.coeff_mod
        if p is None:
            p = q
        if q is None:
            raise Exception('modulus for calculating the inverse polynomial was not specified')
        
        two_poly = conv_poly(self.n)
        two_poly.coefflist[0] = 2
        two_poly.degree = 0
        tmp_poly = self.copy(new_coeff_mod=p)
        inv = tmp_poly.invert_with_prime_mod_coeffs()

        while p < q:
            p = p * p
            two_poly.coeff_mod = p
            inv.coeff_mod = p
            tmp_poly = self.copy(new_coeff_mod=p)
            inv = inv * (two_poly - tmp_poly * inv)

        inv.set_coeff_mod(q)

        return inv




def msgtext_to_msgpoly(msg_text, n, p, secret_generator=secrets.SystemRandom()):
    """converts a string of text, msg_text (considered in UTF-8 encoding), 
       into an array of bytes with given output_length in bits for delivery to NTRU (zero padded on the right to byte boundary),
       or throws an exception if output length is not enough to pack the message"""

    bits_per_coefficient = math.floor(math.log(p, 2))
    output_length = n * bits_per_coefficient

    # 256 is the size of the 160 sha-1 hash field, 16 bit message bit length and 80 bit mandatory padding
    HEADER_SIZE = 256
    msg_text_bytes = msg_text.encode()
    text_bitlength = len(msg_text_bytes) * 8 # text bit length field
    if HEADER_SIZE + text_bitlength > output_length:
        raise ValueError('the text "%s", with %d bytes in length, is too large;'
                         ' only %d bytes of payload are possible to encode with a message length of %d bits'
                         % (msg_text, len(msg_text_bytes), (output_length - HEADER_SIZE) // 8, output_length))

    msg_bits = bytearray(20) # sha-1 hash field
    msg_bits.append((text_bitlength & 0xFF00) >> 8)
    msg_bits.append(text_bitlength & 0xFF)
    for i in range(10): # mandatory random padding field
        msg_bits.append(secret_generator.randrange(0, 256))
    for b in msg_text_bytes:
        msg_bits.append(b)

    bitcount = HEADER_SIZE + text_bitlength
    while bitcount < output_length: # fill out extra random padding up to bit output length
        b = 0
        for i in range(7,-1,-1):
            b |= secret_generator.randrange(0, 2) << i
            bitcount += 1
            if bitcount >= output_length:
                break
        msg_bits.append(b)

    h = hashlib.sha1() # fill out hash field
    h.update(msg_bits[20:])
    msg_bits[0:20] = h.digest()

    #convert a byte like object to a string of bits in a list"""
    msg_bitstring = []
    for b in msg_bits:
        for i in range(7,-1,-1):
            msg_bitstring.append((b & (1 << i)) >> i) # copy ith bit

    # generate a polynomial from a sequence of message bits (encoded as a list of bits).
    # the first n * floor(log(p)) bits in the msg_bits are turned into coefficients, a_0, ..., a_{n - 1}"""
    bitindex = 0
    poly = conv_poly(n, p)
    for c in range(n):
        coeff_val = 0
        for bit in range(bits_per_coefficient):
            coeff_val = 2 * coeff_val + msg_bitstring[bitindex]
            bitindex += 1
        poly.coefflist[c] = coeff_val

    return poly

class decryption_failure(Exception):
    pass

def msgpoly_to_msgtext(poly):

    bits_per_coefficient = math.floor(math.log(poly.coeff_mod, 2))
    maxval = 2 ** bits_per_coefficient
    total_bit_count = bits_per_coefficient * poly.n

    bitlist = []
    for c in poly.coefflist:
        if c >= maxval:
            raise decryption_failure('encoding error: message polynomial coefficient too large')
        for i in range(bits_per_coefficient - 1, -1, -1):
            bitlist.append((c & (1 << i)) >> i) # copy ith bit

    bitcount = 0
    msg_bits = bytearray()
    while bitcount < len(bitlist):
        v = 0
        for i in range(7,-1,-1):
            v |= bitlist[bitcount] << i
            bitcount += 1
            if bitcount >= len(bitlist):
                break
        msg_bits.append(v)

    hasher = hashlib.sha1()
    hasher.update(msg_bits[20:])
    check_hash = hasher.digest()
    hsh = msg_bits[:20]
    if hsh != check_hash:
        raise decryption_failure('encoding error: hash values in message do not match up')

    HEADER_SIZE = 256
    msg_size = msg_bits[20] << 8
    msg_size += msg_bits[21]

    if HEADER_SIZE + msg_size > total_bit_count:
        raise decryption_failure('encoding error: msg_size overflowed the end of the transmitted data')

    if msg_size % 8 != 0:  
        raise decryption_failure('encoding error: must be an incorrect msg_size number of bits in the transmitted data')

    return msg_bits[32:32 + msg_size // 8].decode()


def bits_to_poly(bits, n, p):
    """generate a polynomial from a sequence of bits (encoded as a byte-like object).
       the first n * ceil(log(p)) bits are turned into coefficients, a_0, ..., a_{n - 1}"""

    # convert a byte like object to a string of bits in a list
    bitstring = []
    for b in bits:
        for i in range(7,-1,-1):
            bitstring.append((b & (1 << i)) >> i) # copy ith bit

    bits_per_coefficient = math.ceil(math.log(p, 2))
    if len(bitstring) < n * bits_per_coefficient:
        raise ValueError('expected at least %d * %d = %d bits in byte sequence to be encoded into a polynomial, '
                         'but only %d were found\n'
                         % (n, bits_per_coefficient, n * bits_per_coefficient, len(bitstring)))
    bitindex = 0
    poly = conv_poly(n, p)
    for i in range(n):
        coeff_val = 0
        for b in range(bits_per_coefficient):
            coeff_val = 2 * coeff_val + bitstring[bitindex]
            bitindex += 1
        if coeff_val >= p:
            raise ValueError('encoding error: value of %d for coefficient %d is too large' % (coeff_val, i))
        poly.coefflist[i] = coeff_val
        if coeff_val != 0:
            poly.degree = i

    return poly


def poly_to_bits(poly):
    """returns a sequence of bytes having a bit prefix of length n * ceil(log(p))"""

    bits_per_coefficient = math.ceil(math.log(poly.coeff_mod, 2))
    total_bits = poly.n * bits_per_coefficient

    bitlist = []
    for c in poly.coefflist:
        for i in range(bits_per_coefficient - 1, -1, -1):
            bitlist.append((c & (1 << i)) >> i) # copy ith bit

    bitcount = 0
    msg_bits = bytearray()
    while bitcount < len(bitlist):
        v = 0
        for i in range(7,-1,-1):
            v |= bitlist[bitcount] << i
            bitcount += 1
            if bitcount >= len(bitlist):
                break
        msg_bits.append(v)

    return msg_bits

def generate_random_polynomial(n, ones, minus_ones, secret_generator=secrets.SystemRandom()):

    poly_coeff_list = (n + 1) * [0]
    ones_filled = 0
    minus_ones_filled = 0
    degree = -1
    while ones_filled < ones:
        idx = secret_generator.randrange(0, n)
        if poly_coeff_list[idx] == 0:
            poly_coeff_list[idx] = 1
            ones_filled += 1
            if idx > degree:
                degree = idx
    while minus_ones_filled < minus_ones:
        idx = secret_generator.randrange(0, n)
        if poly_coeff_list[idx] == 0:
            poly_coeff_list[idx] = -1
            minus_ones_filled += 1
            if idx > degree:
                degree = idx

    poly = conv_poly(n)
    poly.coefflist = poly_coeff_list
    poly.degree = degree

    return poly


def ntru_keygen(param_set, secret_generator=secrets.SystemRandom()): # by default use high entropy bits obtained from the operating system
    """generate an NTRU key pair, 
       param_set is a dictionary with keys for parameters n, p, q, d_f, d_g, d_r
       return key_info in the format {'f': ____, 'g': ____, 'f_inv_q': ____, 'f_inv_p': ____, 'h': ____, 'params': _____},
       where the polynomials are bytearray objects."""

    n = param_set['n']
    q = param_set['q']
    p = param_set['p']
    d_f = param_set['d_f']; d_g = param_set['d_g']; d_r = param_set['d_r']
    assert 2 * d_f + 1 < n and 2 * d_g < n and 2 * d_r < n

    # generate f and its inverses in the large and small convolution rings
    valid_f = False
    while not valid_f:

        f = generate_random_polynomial(n, d_f + 1, d_f, secret_generator)

        try:
            # q = b^k, information provided in the instance of ntru
            f_inv_q = f.invert_with_prime_power_mod_coeffs(q, param_set['prime_factor_q'])
        except ArithmeticError as error:
            print('%s: could not invert polynomial %s\n%s\n' % (error.args, f, error.args))
            continue

        try:
            # p is assumed to be a prime
            f_inv_p = f.copy(new_coeff_mod=param_set['p']).invert_with_prime_mod_coeffs()
        except ArithmeticError as error:
            print('%s: could not invert polynomial %s\n%s\n' % (error.args, f, error.args))
            continue

        valid_f = True

    g = generate_random_polynomial(n, d_g, d_g, secret_generator)
    g.set_coeff_mod(q)

    f.set_coeff_mod(q)

    h = (f_inv_q * g).mult_by_term(coeff=p, power=0)

    return {
        'param': param_set,
        'f': poly_to_bits(f),
        'g': poly_to_bits(g),
        'f_inv_q': poly_to_bits(f_inv_q),
        'f_inv_p': poly_to_bits(f_inv_p),
        'h': poly_to_bits(h)
    }

def ntru_encrypt(message, params, h, secret_generator=secrets.SystemRandom()):

    msg_poly = msgtext_to_msgpoly(message, params['n'], params['p'])
    msg_poly.lift()
    msg_poly.set_coeff_mod(params['q'])

    r = generate_random_polynomial(params['n'], ones=params['d_r'], minus_ones=params['d_r'], secret_generator=secret_generator)
    r.set_coeff_mod(params['q'])

    e = bits_to_poly(h, params['n'], params['q']) * r + msg_poly

    return poly_to_bits(e)

def ntru_decrypt(encrypted_message, params, key_info):

    a = bits_to_poly(key_info['f'], params['n'], params['q']) * bits_to_poly(encrypted_message, params['n'], params['q'])
    a.lift()
    a.set_coeff_mod(params['p'])

    m = bits_to_poly(key_info['f_inv_p'], params['n'], params['p']) * a

    return msgpoly_to_msgtext(m)
    



def test_expr_equality(test_cases):
    """test the equality of the value of a bunch of expressions; input taken in the form
       [
           (test_expr1, expected_result1),
           .
           .
           .
           (test_exprN, expected_resultN)
       ]
       note that the expressions should be strings (or convertible to string), 
       as they will be executed with eval, and then compared via __eq__"""
    successcount = 0
    for i in range(len(test_cases)):
        result = eval(str(test_cases[i][0]))
        expected_result = eval(str(test_cases[i][1]))
        if result != expected_result:
            print('test %d FAILED!\nexpression "%s"\nyielded value "%s"\nbut we expected value"%s"\n'
                  % (i, test_cases[i][0], repr(result), repr(expected_result)))
        else:
            print('test %d PASSED:\nexpression "%s"\nyielded value "%s"\nwhich is what we expected\n'
                  % (i, test_cases[i][0], repr(result)))
            successcount += 1
    print('%d out of %d tests passed\n\n' % (successcount, len(test_cases)))




def test_ntru(param_sets, messages):

    rand_gen = random.Random(42) # seeded generator for testing
    passed = 0; failed = 0
    
    for params in param_sets:
        print('testing the parameter set %s\n' % params)
        key_info = ntru_keygen(params, rand_gen)
        print('take note that \n',
              'f = %s\n' % bits_to_poly(key_info['f'], params['n'], params['q']),
              'f_inv_q = %s\n' % bits_to_poly(key_info['f_inv_q'], params['n'], params['q']),
              'f_inv_p = %s\n' % bits_to_poly(key_info['f_inv_p'], params['n'], params['p']),
              'g = %s\n' % bits_to_poly(key_info['g'], params['n'], params['q']),
              'h = %s\n' % bits_to_poly(key_info['h'], params['n'], params['q']),
              'are the polynomials of the generated key pair\n',
              'and\n',
              'f = %s\n' % key_info['f'],
              'f_inv_q = %s\n' % key_info['f_inv_q'],
              'f_inv_p = %s\n' % key_info['f_inv_p'],
              'g = %s\n' % key_info['g'],
              'h = %s\n' % key_info['h'],
              'are the raw encoded bits',
              sep='')

        for msg in messages:
            msg_bytes = bytearray(msg.encode(encoding='utf-8'))
            print('testing the message "%s" of length %d bytes\n' % (msg, len(msg_bytes)))
            e = ntru_encrypt(msg, params, key_info['h'], rand_gen)
            print('take note that the encrypted message is encoded as the polynomial %s\n'
                  % bits_to_poly(e, params['n'], params['q']),
                  'and\n',
                  '%s\n' % e,
                  'are the raw bytes to transmitted\n',
                  sep='')
            try:
                m = ntru_decrypt(e, params, key_info)
            except decryption_failure as de:
                print('failed to decrypt due to %s, %s\n' % (e.args, e))
                print('FAILED')
                failed += 1
                continue

            print('the decrypted message is %s\n' % m)
            if m == msg:
                print('PASSED')
                passed += 1
            else:
                print('FAILED')
                failed += 1

    print('results:\npassed %d tests, failed %d' % (passed, failed))

def test_extended_euclidean_algorithm(arglist):
    successcount = 0; i = 0
    for a, b, correct_g in arglist:
        x, y, g = extended_euclidean_algorithm(a, b)
        if a * x + b * y != g or g != correct_g:
            print('\nFAILED test %d: extended_euclid(%d, %d) returned x = %d, y = %d, g = %d\n'
                  'where %d * %d + %d * %d = %d, and expected gcd was %d\n'
                  % (i, a, b, x, y, g, a, x, b, y, g, correct_g))
        else:
            print('\nPASSED test %d: extended_euclid(%d, %d) returned x = %d, y = %d, g = %d\n'
                  'where %d * %d + %d * %d = %d, and expected gcd was %d\n'
                  % (i, a, b, x, y, g, a, x, b, y, g, correct_g))
            successcount += 1
        i += 1
    print('%d out of %d tests passed\n\n' % (successcount, len(arglist)))

def test_poly_extended_euclidean_algorithm(arglist):
    successcount = 0; i = 0
    for a, b, correct_g in arglist:
        x, y, g = conv_poly.poly_extended_euclidean_algorithm(a, b)
        if a * x + b * y != g or conv_poly.make_monic(g) != conv_poly.make_monic(correct_g):
            print('\nFAILED test %d: poly_extended_extended_euclid(%s, %s) returned x = (%s), y = (%s), g = (%s)\n'
                  'where (%s) * (%s) + (%s) * (%s) = (%s), and expected gcd was (%s)\n'
                  % (i, a, b, x, y, g, a, x, b, y, a*x + b*y, correct_g))
        else:
            print('\nPASSED test %d: poly_extended_extended_euclid(%s, %s) returned x = (%s), y = (%s), g = (%s)\n'
                  'where (%s) * (%s) + (%s) * (%s) = (%s), and expected gcd was (%s)\n'
                  % (i, a, b, x, y, g, a, x, b, y, g, correct_g))
            successcount += 1
        i += 1
    print('%d out of %d tests passed\n\n' % (successcount, len(arglist)))

def run_unit_tests():

    test_extended_euclidean_algorithm(
        # each test case has format: (a, b, gcd(a, b))
        [(16, 4, 4), (12, 8, 4), (-12, 8, 4), (1000000007, 15, 1),
         (-1, -13, 1)]
    )

    test_poly_extended_euclidean_algorithm(
        # each test case has format: (a, b, gcd(a, b))
        [(conv_poly(polynomial='x + 4', p=1000000007, n=107) * conv_poly(polynomial='x + 7', p=1000000007, n=107) * conv_poly(polynomial='x + 4', p=1000000007, n=107),
          conv_poly(polynomial='x + 5', p=1000000007, n=107) * conv_poly(polynomial='x + 7', p=1000000007, n=107) * conv_poly(polynomial='x + 4', p=1000000007, n=107),
          conv_poly(polynomial='x + 4', p=1000000007, n=107) * conv_poly(polynomial='x + 7', p=1000000007, n=107))]
    )

    poly_extended_euclidean_algorithm_test_cases = [
        ("conv_poly.poly_extended_euclidean_algorithm(conv_poly(polynomial='x + 4', p=1000000007, n=107) * conv_poly(polynomial='x + 7', p=1000000007, n=107) * conv_poly(polynomial='x + 4', p=1000000007, n=107), "
                                                     "conv_poly(polynomial='x + 5', p=1000000007, n=107) * conv_poly(polynomial='x + 7', p=1000000007, n=107) * conv_poly(polynomial='x + 4', p=1000000007, n=107))[2].make_monic()",

         "conv_poly(polynomial='x + 4', p=1000000007, n=107) * conv_poly(polynomial='x + 7', p=1000000007, n=107)")
    ]
    test_expr_equality(poly_extended_euclidean_algorithm_test_cases)



    poly_test_cases = [
        ("conv_poly(polynomial='x^2 + x', p=2, n=107) + conv_poly(polynomial='x + 1', p=2, n=107)",
         "conv_poly(polynomial='x^2 + 1', p=2, n=107)"),
    ]
    test_expr_equality(poly_test_cases)

    

    test_ntru([
        # parameter sets specified in the IEEE STD 1363.1-2008, "public key cryptography based on hard lattice problems"

        # note: q = b^k
        # optimized for "size". 
        {'param_set': 'ees401ep1', 'n': 401, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 113, 'd_g': 133, 'd_r': 113}, # 112-bit security level
        {'param_set': 'ees449ep1', 'n': 449, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 134, 'd_g': 149, 'd_r': 134}, # 128-bit security level
        {'param_set': 'ees677ep1', 'n': 677, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 157, 'd_g': 225, 'd_r': 157}, # 192-bit security level
        {'param_set': 'ees1087ep2', 'n': 1087, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 120, 'd_g': 362, 'd_r': 120}, # 256-bit security level

        # optimized for "cost", defined as running_time^2 * size. 
        {'param_set': 'ees541ep1', 'n': 541, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 49, 'd_g': 180, 'd_r': 49}, # 112-bit decurity level
        {'param_set': 'ees613ep1', 'n': 613, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 55, 'd_g': 204, 'd_r': 55}, # 128-bit security level
        {'param_set': 'ees887ep1', 'n': 887, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 81, 'd_g': 295, 'd_r': 81}, # 192-bit security level
        {'param_set': 'ees1171ep1', 'n': 1171, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 106, 'd_g': 390, 'd_r': 106}, # 256-bit security level

        # optimized for running time 
        {'param_set': 'ees659ep1', 'n': 659, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 38, 'd_g': 219, 'd_r': 38}, # 112-bit decurity level
        {'param_set': 'ees761ep1', 'n': 761, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 42, 'd_g': 253, 'd_r': 42}, # 128-bit security level
        {'param_set': 'ees1087ep1', 'n': 1087, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 63, 'd_g': 362, 'd_r': 63}, # 192-bit security level
        {'param_set': 'ees1499ep1', 'n': 1499, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 79, 'd_g': 499, 'd_r': 79}, # 256-bit security level
    ],
    [
        'mc938-2s2017',
        'oi',
        'tchau',
        '99 bottles',
        'g4389hg8hg',
        'cryptobunda'
    ]
    )

if __name__ == '__main__':
    #import ipdb
    #ipdb.set_trace()
    
    run_unit_tests()

    while 1:
        print('enter a line with a message to see it encrypted and decrypted. enter an empty line to quit')
        msg = sys.stdin.readline()
        if msg == '':
            break
        test_ntru([{'param_set': 'ees761ep1', 'n': 761, 'p': 3, 'q': 2048, 'prime_factor_q': 2, 'd_f': 42, 'd_g': 253, 'd_r': 42}], # 128-bit security level
                  [msg])

