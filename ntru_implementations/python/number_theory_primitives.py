#!/usr/bin/env python3

"""various number theory related primitives, as well as
   various routines for unit testing those primitives"""


import re # for parsing the polynomial strings 


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

def test_extended_euclidean_algorithm(arglist):
    for a, b, correct_g in arglist:
        x, y, g = extended_euclidean_algorithm(a, b)
        if a * x + b * y != g or g != correct_g:
            print('\nFAILED!: extended_euclid(%d, %d) returned x = %d, y = %d, g = %d\n'
                  'where %d * %d + %d * %d = %d, and expected gcd was %d\n'
                  % (a, b, x, y, g, a, x, b, y, g, correct_g))
        else:
            print('\nPASSED: extended_euclid(%d, %d) returned x = %d, y = %d, g = %d\n'
                  'where %d * %d + %d * %d = %d, and expected gcd was %d\n'
                  % (a, b, x, y, g, a, x, b, y, g, correct_g))


def mod_inverse(num, m):
    """calculate multiplicative inverse of num, modulo a positive integer m"""
    assert(m > 0)

    a, b, g = extended_euclidean_algorithm(num, m)

    if g != 1:
        raise ValueError('the number %d does not have a multiplicative inverse modulo %d'
                         % (num, m))
    return a % m


def mod_exp(num, n, m):
    """raise a number num to the power n, """
    """the result being considered modulo m, a positive integer"""
    if m <= 0:
        raise ValueError('expected a positive modulus in mod_exp operation')
    if num % m == 0:
        return 0

    exponent = abs(n)
    result = 1
    while exponent != 0: # multiply and square algorithm starting with the least significant bit of exponent
        if exponent % 2 == 1:
            result = (result * num) % m
        num = (num * num) % m
        exponent //= 2
    if n < 0:
        result = mod_inverse(result, m)

    return result


def poly_extended_euclidean_algorithm(x, y):
    """extended euclidean algorithm - only for polynomials"""
   
   # make sure to return a monic polynomial as the gcd. return 0 if both polys are 0.
    if y == poly('0', p=y.p):
        if x == poly('0', p=x.p):
            monic_gcd = poly('0', p=x.p) # pathological case of gcd(0, 0)
        else:
            make_monic = mod_inverse(x.leading_coeff(), x.p)
            monic_gcd = x * make_monic
            return (poly(str(make_monic), p=x.p), poly('0', p=x.p), monic_gcd) 

    _a, _b, g = poly_extended_euclidean_algorithm(y, x % y)
    a, b = _b, _a - _b * (x / y)

    return (a, b, g)


def poly_mod_inverse(x, mod_poly):
    a, b, g = poly_extended_euclidean_algorithm(x, mod_poly)
    if g != poly('1', p=x.p):
        raise ValueError('the polynomial %s does not have a multiplicative inverse modulo %s'
                         % (repr(x), repr(mod_poly)))
    return a % mod_poly


def poly_mod_exp(x, n, mod_poly):
    if x % mod_poly == poly('0', p=x.p):
        return poly('0', p=x.p)

    exponent = abs(n)
    result = poly('1', p=x.p)
    while exponent != 0: # multiply and square algorithm starting with the least significant bit of exponent
        if exponent % 2 == 1:
            result = (result * x) % mod_poly
        x = (x * x) % mod_poly
        exponent //= 2
    if n < 0:
        result = poly_mod_inverse(result, mod_poly)

    return result


def coefflist2str(coefflist):
    """convert a coefficient list of a polynomial to a string representation"""
    if coefflist == []:
        s = '0'
    else:
        s = ''
        for i in range(len(coefflist) - 1, -1, -1):
            if coefflist[i] != 0:
                if coefflist[i] > 0:
                    if i < len(coefflist) - 1:
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
    return s.strip()


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


def num2binarycoefflist(polynomial):
    """convert an integer (whose bits represent a binary polynomial) """
    """to a list of the binary coefficients of that polynomial"""
    coefflist = []
    while polynomial != 0:
        coefflist.append(polynomial % 2)
        polynomial //= 2
    return coefflist


def binarycoefflist2num(coefflist):
    """convert a binary list of coefficients of a polynomial to a numerical (non-negative integer) representation, """
    """with a bit for each coefficient"""
    result = 0
    exponent = 1
    for i in range(len(coefflist)):
        result += (coefflist[i] % 2) * exponent
        exponent *= 2
    return result


class poly():
    """represent a polynomial with coefficients in a finite field of (prime) order p. """
    """the list of coefficients has the degree 0, 1, 2, ..., degree(poly) terms in order. """
    """the last term is non-zero and gives the polynomial its degree. """
    """the zero polynomial is represented by an empty list; it is defined to have degree -1"""

    def __init__(self, polynomial='0', p=2):
        if type(polynomial) is int:
            if p != 2:
                raise ValueError('since a polynomial was specified as a number, the coefficients must belong to prime field of order 2')
            self.coefflist = num2binarycoefflist(polynomial)
        else:
            self.coefflist = str2coefflist(polynomial)
        self.p = p
        for i in range(len(self.coefflist)):
            self.coefflist[i] %= self.p

    def degree(self):
        return len(self.coefflist) - 1

    def leading_coeff(self):
        if self.degree() >= 0:
            return self.coefflist[-1]
        else:
            return 0

    def copy(self):
        new_poly = poly()
        new_poly.coefflist = list(self.coefflist)
        new_poly.p = self.p
        return new_poly

    def __divmod__(self, rhs):
        if rhs.degree() < 0:
            raise ArithmeticError('attempted division by the zero polynomial')
        q, r = poly('0', self.p), self.copy()
        while rhs.degree() <= r.degree():
            c = r.leading_coeff() * mod_inverse(rhs.leading_coeff(), self.p)
            partial_q = poly('%d x^%d' % (c, r.degree() - rhs.degree()), self.p)
            q += partial_q
            r -= partial_q * rhs
        return q, r

    def __truediv__(self, rhs):
        q, _ = divmod(self, rhs)
        return q

    def __mod__(self, rhs):
        _, r = divmod(self, rhs)
        return r

    def __add__(self, rhs, subtract=False):
        new_poly = poly('0', self.p)
        for i in range(0, min(self.degree(), rhs.degree()) + 1):
            if subtract is False:
                new_poly.coefflist.append((self.coefflist[i] + rhs.coefflist[i]) % self.p)
            else:
                new_poly.coefflist.append((self.coefflist[i] - rhs.coefflist[i]) % self.p)                
        if self.degree() < rhs.degree():
            for i in range(self.degree()+1, rhs.degree()+1):
                if subtract is False:
                    new_poly.coefflist.append(rhs.coefflist[i])
                else:
                    new_poly.coefflist.append(-rhs.coefflist[i] % self.p)                    
        else:
            for i in range(rhs.degree()+1, self.degree()+1):
                new_poly.coefflist.append(self.coefflist[i])
        # maintain the invariant: highest degree term non-zero
        for i in range(len(new_poly.coefflist) - 1, -1, -1):
            if new_poly.coefflist[i] == 0:
                new_poly.coefflist.pop()
            else:
                return new_poly
        return new_poly # result was the zero polynomial

    def __sub__(self, rhs):
        return self.__add__(rhs, subtract=True)

    def __neg__(self):
        new_poly = poly('0', self.p)
        for i in range(len(self.coefflist)):
            new_poly.coefflist.append(-self.coefflist[i] % self.p)
        return new_poly

    def __mul__(self, rhs):
        if type(rhs) is int: # handle the convenient case of scalar multiplication
            return self * poly(str(rhs), p=self.p)
            
        new_poly = poly('0', self.p)
        if self.degree() < 0 or rhs.degree() < 0:
            return new_poly # special case of zero polynomial
        for i in range(self.degree() + rhs.degree() + 1):
            coeff = 0
            for j in range(max(0, i - rhs.degree()), min(self.degree(), i) + 1):
                coeff += self.coefflist[j] * rhs.coefflist[i - j]
            new_poly.coefflist.append(coeff % self.p)
        return new_poly

    def __str__(self):
        return coefflist2str(self.coefflist)

    def __repr__(self):
        return 'poly(polynomial=\'%s\', p=%d)' % (coefflist2str(self.coefflist), self.p)

    def __eq__(self, rhs):
        return (True if self.p == rhs.p and 
                       self.coefflist == rhs.coefflist
                     else False)
    def __ne__(self, rhs):
        return not self == rhs


class mod_poly():
    """represent a polynomial 
       with coefficients modulo p, 
       modulo the polynomial mod_poly (not necessarily irreducible)"""

    def __init__(self, polynomial='0', p=2, mod_poly='x'):
        self.poly = poly(polynomial, p)
        self.mod_poly = poly(mod_poly, p)
        self.poly = self.poly % self.mod_poly

    def __add__(self, rhs, subtract=False):
        new_poly = mod_poly()
        if subtract:
            new_poly.poly = self.poly - rhs.poly
        else:
            new_poly.poly = self.poly + rhs.poly
        new_poly.mod_poly = self.mod_poly.copy()
        return new_poly

    def __sub__(self, rhs):
        return mod_poly.__add__(self, rhs, subtract=True)

    def __neg__(self):
        new_poly = mod_poly()
        new_poly.poly = -self.poly
        new_poly.mod_poly = self.mod_poly.copy()
        return new_poly

    def __truediv__(self, rhs):
        return self * rhs.invert()

    def __mul__(self, rhs):
        new_poly = mod_poly()
        new_poly.poly = (self.poly * rhs.poly) % self.mod_poly
        new_poly.mod_poly = self.mod_poly.copy()
        return new_poly

    def __str__(self):
        return str(self.poly)

    def __repr__(self):
        return ('mod_poly(polynomial=\'%s\', p=%d, mod_poly=\'%s\')' 
                % (str(self.poly), self.poly.p, str(self.mod_poly)))

    def __eq__(self, rhs):
        return (True if self.poly == rhs.poly and self.mod_poly == rhs.mod_poly
                     else False)
    
    def __ne__(self, rhs):
        return not self == rhs

    def invert(self):
        new_poly = mod_poly()
        new_poly.poly = poly_mod_inverse(self.poly, self.mod_poly)
        new_poly.mod_poly = self.mod_poly.copy()
        return new_poly



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
                  % (i, test_cases[i][1], repr(result)))
            successcount += 1
    print('%d out of %d tests passed' % (successcount, len(test_cases)))


def run_unit_tests():

    test_extended_euclidean_algorithm(
        # each test case has format: (a, b, gcd(a, b))
        [(16, 4, 4), (12, 8, 4), (-12, 8, 4), (1000000007, 15, 1),
         (-1, -13, 1)]
    )

    mod_exp_test_cases = [
        ("mod_exp(num=3, n=17, m=174311)",
         "150023"),
        
        ("mod_exp(num=3, n=-17, m=174311)",
         "31169")
    ]

    poly_test_cases = [
        ("poly(polynomial='x^2 + x', p=2) + poly(polynomial='x + 1', p=2)",
         "poly(polynomial='x^2 + 1', p=2)"),
    ]

    mod_poly_test_cases = [
        ("mod_poly(polynomial='x^6', p=2, mod_poly='x^3 - 1')",
         "mod_poly(polynomial='1', p=2, mod_poly='x^3 - 1')"),

        ("mod_poly(polynomial='x^2 + 1', p=2, mod_poly='x^3 - 1') * mod_poly(polynomial='0', p=2, mod_poly='x^3 - 1')",
         "mod_poly(polynomial='0', p=2, mod_poly='x^3 - 1')"),
        
        ("mod_poly(polynomial='x^2 + 1', p=2, mod_poly='x^3 - 1') * mod_poly(polynomial='x^6', p=2, mod_poly='x^3 - 1')",
         "mod_poly(polynomial='x^2 + 1', p=2, mod_poly='x^3 - 1')"),
        
        ("mod_poly(polynomial='x^2 + x', p=2, mod_poly='x^3 - 1') + mod_poly(polynomial='x + x +x^2 + x', p=2, mod_poly='x^3 - 1')",
         "mod_poly(polynomial=' 0', p=2, mod_poly='x^3 - 1')"),
        
        ("mod_poly(polynomial='x + 2', p=2, mod_poly='x^2 + 1') * mod_poly(polynomial='x + 2', p=2, mod_poly='x^2 + 1')",
         "mod_poly(polynomial='1', p=2, mod_poly='x^2 + 1')"),
 
        ("mod_poly(polynomial='1', p=174311) / mod_poly(polynomial=str(3**17), p=174311)",
         "mod_poly(polynomial='31169', p=174311, mod_poly='x')"),
        
        ("mod_poly(0x9f, p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')",
         "mod_poly(polynomial='x^7 + x^4 + x^3 + x^2 + x + 1', p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')"),
        
        ("mod_poly(0xd8, p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')",
         "mod_poly(polynomial='x^7 + x^6 + x^4 + x^3', p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')"),
        
        ("mod_poly(0x9f, p=2, mod_poly='x^8 + x^4 + x^3 + x + 1') * mod_poly(0xd8, p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')",
         "mod_poly(polynomial='x^7 + x^6 + x^5 + x^3', p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')"),

        ("hex(binarycoefflist2num((mod_poly(0x9f, p=2, mod_poly='x^8 + x^4 + x^3 + x + 1') * mod_poly(0xd8, p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')).poly.coefflist))",
         "hex(0xe8)"),
        
        ("mod_poly(0x8E, p=2, mod_poly='x^8 + x^4 + x^3 + x + 1') * mod_poly('x', p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')",
         "mod_poly(polynomial='x^2 + x + 1', p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')"),
        
        ("mod_poly(0x8E, p=2, mod_poly='x^8 + x^4 + x^3 + x + 1') * mod_poly('x', p=2, mod_poly='x^8 + x^4 + x^3 + x + 1') * mod_poly('x', p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')",
         "mod_poly(polynomial='x^3 + x^2 + x', p=2, mod_poly='x^8 + x^4 + x^3 + x + 1')"),
        
        ("mod_poly('x^2', p=2, mod_poly='x^3 - 1').invert()",
         "mod_poly(polynomial='x', p=2, mod_poly='x^3 + 1')")
    ]

    test_expr_equality(mod_exp_test_cases + poly_test_cases + mod_poly_test_cases)


if __name__ == '__main__':
    run_unit_tests()