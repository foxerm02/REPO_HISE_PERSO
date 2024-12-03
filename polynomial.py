from typing import List, Tuple, Optional, Iterator
from dataclasses import dataclass
from py_ecc.bls12_381 import FQ, field_modulus

class Scalar:
    def __init__(self, value: int):
        self.value = value % field_modulus
    
    @classmethod
    def zero(cls) -> 'Scalar':
        return cls(0)
    
    @classmethod
    def one(cls) -> 'Scalar':
        return cls(1)
    
    def __add__(self, other: 'Scalar') -> 'Scalar':
        return Scalar((self.value + other.value) % field_modulus)
    
    def __sub__(self, other: 'Scalar') -> 'Scalar':
        return Scalar((self.value - other.value) % field_modulus)
    
    def __mul__(self, other: 'Scalar') -> 'Scalar':
        return Scalar((self.value * other.value) % field_modulus)
    
    def __eq__(self, other: 'Scalar') -> bool:
        return self.value == other.value
    
    def neg(self) -> 'Scalar':
        return Scalar((-self.value) % field_modulus)
    
    def invert(self) -> Optional['Scalar']:
        if self.value == 0:
            return None
        # Utilise le petit théorème de Fermat pour l'inversion modulaire
        return Scalar(pow(self.value, field_modulus - 2, field_modulus))

@dataclass
class Polynomial:
    degree: int
    coeffs: List[Scalar]
    
    def __eq__(self, other: 'Polynomial') -> bool:
        if self.degree != other.degree:
            return False
        return all(l == r for l, r in zip(self.coeffs[:self.degree + 1], 
                                         other.coeffs[:other.degree + 1]))
    
    def is_zero(self) -> bool:
        return self.degree == 0 and self.coeffs[0] == Scalar.zero()
    
    @classmethod
    def new_zero(cls) -> 'Polynomial':
        return cls(0, [Scalar.zero()])
    
    @classmethod
    def from_scalar(cls, scalar: Scalar) -> 'Polynomial':
        return cls(0, [scalar])
    
    @classmethod
    def new_monic_of_degree(cls, degree: int) -> 'Polynomial':
        return cls(degree, [Scalar.one()] * (degree + 1))
    
    @classmethod
    def new_single_term(cls, degree: int) -> 'Polynomial':
        coeffs = [Scalar.zero()] * (degree + 1)
        coeffs[degree] = Scalar.one()
        return cls(degree, coeffs)
    
    @classmethod
    def new_zero_with_size(cls, cap: int) -> 'Polynomial':
        return cls(0, [Scalar.zero()] * cap)
    
    @classmethod
    def new(cls, coeffs: List[Scalar]) -> 'Polynomial':
        degree = cls.compute_degree(coeffs, len(coeffs) - 1)
        return cls(degree, coeffs)
    
    @classmethod
    def new_from_coeffs(cls, coeffs: List[Scalar], degree: int) -> 'Polynomial':
        return cls(degree, coeffs)
    
    @staticmethod
    def compute_degree(coeffs: List[Scalar], upper_bound: int) -> int:
        for i in range(upper_bound, -1, -1):
            if coeffs[i] != Scalar.zero():
                return i
        return 0
    
    def truncate(self, degree: int) -> None:
        self.degree = degree
        self.coeffs = self.coeffs[:degree + 1]
    
    def reverse(self) -> None:
        self.coeffs = self.coeffs[:self.num_coeffs()]
        self.coeffs.reverse()
    
    def shrink_degree(self) -> None:
        self.degree = self.compute_degree(self.coeffs, self.degree)
    
    def fixup_degree(self) -> None:
        self.degree = self.compute_degree(self.coeffs, len(self.coeffs) - 1)
    
    def lead(self) -> Scalar:
        return self.coeffs[self.degree]
    
    def constant(self) -> Scalar:
        return self.coeffs[0]
    
    def num_coeffs(self) -> int:
        return self.degree + 1
    
    
    def eval(self, x: Scalar) -> Scalar:
        if self.degree == 0:
            return self.coeffs[0]
            
        res = self.coeffs[self.degree]
        for i in range(self.degree - 1, -1, -1):
            res = res * x + self.coeffs[i]
        return res
    

    def __add__(self, other: 'Polynomial') -> 'Polynomial':
        max_degree = max(self.degree, other.degree)
        result_coeffs = [Scalar.zero()] * (max_degree + 1)
        
        for i in range(len(result_coeffs)):
            if i <= self.degree:
                result_coeffs[i] = self.coeffs[i]
            if i <= other.degree:
                result_coeffs[i] = result_coeffs[i] + other.coeffs[i]
                
        return Polynomial(max_degree, result_coeffs)
    
    def __mul__(self, other: 'Polynomial') -> 'Polynomial':
        result = Polynomial.new_zero_with_size(self.degree + other.degree + 1)
        
        for i in range(self.num_coeffs()):
            for j in range(other.num_coeffs()):
                result.coeffs[i + j] = result.coeffs[i + j] + (self.coeffs[i] * other.coeffs[j])
        
        result.degree = self.degree + other.degree
        return result
    
    def best_mul(self, other: 'Polynomial') -> 'Polynomial':
        return self * other
    
    def long_division(self, divisor: 'Polynomial') -> Tuple['Polynomial', Optional['Polynomial']]:
        if self.is_zero():
            return (Polynomial.new_zero(), None)
        elif divisor.is_zero():
            raise ValueError("divisor must not be zero!")
        elif self.degree < divisor.degree:
            return (Polynomial.new_zero(), self.clone())
        else:
            remainder = self.clone()
            quotient = Polynomial.new_from_coeffs(
                [Scalar.zero()] * (self.degree - divisor.degree + 1),
                self.degree - divisor.degree
            )
            
            lead_inverse = divisor.lead().invert()
            if lead_inverse is None:
                raise ValueError("Failed to compute inverse of leading coefficient")
                
            while not remainder.is_zero() and remainder.degree >= divisor.degree:
                factor = remainder.lead() * lead_inverse
                i = remainder.degree - divisor.degree
                quotient.coeffs[i] = factor
                
                for j in range(divisor.num_coeffs()):
                    remainder.coeffs[i + j] = remainder.coeffs[i + j] - (divisor.coeffs[j] * factor)
                
                remainder.shrink_degree()
            
            if remainder.is_zero():
                return (quotient, None)
            else:
                return (quotient, remainder)

    def clone(self) -> 'Polynomial':
        return Polynomial(self.degree, self.coeffs.copy())
    
    @classmethod
    def lagrange_interpolation(cls, xs: List[Scalar], ys: List[Scalar]) -> 'Polynomial':
        assert len(xs) == len(ys)
        
        if len(xs) == 1:
            coeffs = [ys[0]]  # Cas spécial pour un seul point
            return cls.new_from_coeffs(coeffs, 0)
            
        tree = SubProductTree.new_from_points(xs)
        
        m_prime = tree.product.clone()
        for i in range(1, m_prime.num_coeffs()):
            m_prime.coeffs[i] = m_prime.coeffs[i] * Scalar(i)
        
        m_prime.coeffs = m_prime.coeffs[1:]  # Supprime le premier coefficient
        m_prime.degree -= 1
        
        cs = []
        evals = m_prime.multi_eval(xs)
        for i, (c, y) in enumerate(zip(evals, ys)):
            inv = c.invert()
            if inv is None:
                raise ValueError(f"Failed to compute inverse at index {i}")
            cs.append(y * inv)
            
        return tree.linear_mod_combination(cs)
    
    @staticmethod   
    def lagrange_coefficients(xs: List[Scalar]) -> List[Scalar]:
        """Calcule les coefficients de Lagrange pour l'interpolation à x=0."""
        assert len(xs) > 1, "undefined for 1 point"

        tree = SubProductTree.new_from_points(xs)
        vanishing_at_0 = tree.product.eval(Scalar.zero())  # V_T(0)
        
        # V_{T \ {j}}(0) = V_T(0) / (0 - j)
        nums = []
        for j in xs:
            neg_j = Scalar.zero() - j  # 0 - j
            inv = neg_j.invert()
            if inv is None:
                raise ValueError("Failed to compute inverse")
            nums.append(vanishing_at_0 * inv)

        m_prime = tree.product.clone()
        for i in range(1, m_prime.num_coeffs()):
            m_prime.coeffs[i] = m_prime.coeffs[i] * Scalar(i)
        
        m_prime.coeffs.pop(0)  # Supprime le premier coefficient
        m_prime.degree -= 1

        cs = []
        evals = m_prime.multi_eval(xs)
        for i, c in enumerate(evals):
            inv = c.invert()
            if inv is None:
                raise ValueError(f"Failed to compute inverse at index {i}")
            cs.append(nums[i] * inv)

        return cs

    
    def multi_eval(self, xs: List[Scalar]) -> List[Scalar]:
        # Suppression de l'assertion qui n'est pas nécessaire ici
        tree = SubProductTree.new_from_points(xs)
        return tree.eval(xs, self)

class SubProductTree:
    def __init__(self, product: Polynomial, left: Optional['SubProductTree'] = None, 
                 right: Optional['SubProductTree'] = None):
        self.product = product
        self.left = left
        self.right = right
    
    @classmethod
    def new_from_points(cls, xs: List[Scalar]) -> 'SubProductTree':
        if len(xs) == 1:
            return cls(
                product=Polynomial.new_from_coeffs([xs[0].neg(), Scalar.one()], 1),
                left=None,
                right=None
            )
        else:
            n = len(xs)
            mid = n // 2
            left = cls.new_from_points(xs[:mid])
            right = cls.new_from_points(xs[mid:])
            return cls(
                product=left.product.best_mul(right.product),
                left=left,
                right=right
            )
    
    def eval(self, xs: List[Scalar], f: Polynomial) -> List[Scalar]:
        n = len(xs)
        
        if n == 1:
            return [f.eval(xs[0])]
        else:
            mid = n // 2
            
            _, r0 = f.long_division(self.left.product)
            _, r1 = f.long_division(self.right.product)
            
            if r0 is None or r1 is None:
                raise ValueError("Unexpected None remainder in division")
                
            l0 = self.left.eval(xs[:mid], r0)
            l1 = self.right.eval(xs[mid:], r1)
            
            return l0 + l1
    
    def linear_mod_combination(self, cs: List[Scalar]) -> Polynomial:
        n = len(cs)
        
        if n == 1:
            return Polynomial.new_from_coeffs([cs[0]], 0)
        else:
            mid = n // 2
            l = self.left.linear_mod_combination(cs[:mid])
            r = self.right.linear_mod_combination(cs[mid:])
            
            return self.right.product.best_mul(l) + self.left.product.best_mul(r)

import unittest
from polynomial import Polynomial, Scalar

class TestPolynomial(unittest.TestCase):
    def test_long_division(self):
        # Test case 1: 3x^4 - 5x^2 + 3 / x + 2
        x = Polynomial.new([
            Scalar(3),        # constant term
            Scalar(0),        # x^1
            Scalar(-5),       # x^2
            Scalar(0),        # x^3
            Scalar(3)         # x^4
        ])
        
        y = Polynomial.new([
            Scalar(2),        # constant term
            Scalar(1),        # x^1
            Scalar(0),        # x^2
            Scalar(0),        # x^3
            Scalar(0)         # x^4
        ])
        
        q, r = x.long_division(y)
        
        # Check remainder
        self.assertIsNotNone(r)
        expected_r = Polynomial.new([
            Scalar(31),
            Scalar(0),
            Scalar(0),
            Scalar(0),
            Scalar(0)
        ])
        self.assertEqual(r, expected_r)
        
        # Check quotient
        expected_q = Polynomial.new([
            Scalar(-14),
            Scalar(7),
            Scalar(-6),
            Scalar(3),
            Scalar(0)
        ])
        self.assertEqual(q, expected_q)

    def test_eval_basic(self):
        # y(x) = x^5 + 4x^3 + 7x^2 + 34
        polynomial = Polynomial.new([
            Scalar(34),    # constant term
            Scalar(0),     # x^1
            Scalar(7),     # x^2
            Scalar(4),     # x^3
            Scalar(0),     # x^4
            Scalar(1)      # x^5
        ])
        
        # y(0) = 34
        self.assertEqual(polynomial.eval(Scalar(0)), Scalar(34))
        
        # y(1) = 46
        self.assertEqual(polynomial.eval(Scalar(1)), Scalar(46))
        
        # y(5) = 3834
        self.assertEqual(polynomial.eval(Scalar(5)), Scalar(3834))

    def test_interpolation(self):
        # Test case 1: Single point
        xs = [Scalar(2)]
        ys = [Scalar(8)]
        
        interpolation = Polynomial.lagrange_interpolation(xs, ys)
        
        for x, y in zip(xs, ys):
            self.assertEqual(interpolation.eval(x), y)
        
        # Test case 2: Multiple points
        xs = [Scalar(x) for x in [2, 5, 7, 90, 111, 31, 29]]
        ys = [Scalar(y) for y in [8, 1, 43, 2, 87, 122, 13]]
        
        interpolation = Polynomial.lagrange_interpolation(xs, ys)
        
        for x, y in zip(xs, ys):
            self.assertEqual(interpolation.eval(x), y)

    def verify_tree(self, tree):
        if tree.left is not None and tree.right is not None:
            expected_product = tree.left.product.best_mul(tree.right.product)
            self.assertEqual(tree.product, expected_product)

    def test_new_subproduct_tree(self):
        xs = [Scalar(x) for x in [2, 5, 7, 90, 111, 31, 29]]
        tree = SubProductTree.new_from_points(xs)
        self.verify_tree(tree)
        
        xs = [Scalar(x) for x in [2, 5, 7, 90, 111]]
        tree = SubProductTree.new_from_points(xs)
        self.verify_tree(tree)

    def test_fast_multi_eval(self):
        polynomial = Polynomial.new([Scalar(x) for x in [2, 5, 7, 90, 111]])
        xs = [Scalar(x) for x in range(1, 9)]  # [1, 2, 3, 4, 5, 6, 7, 8]
        
        # Fast evaluation
        fast = polynomial.multi_eval(xs)
        fast = fast[:len(xs)]
        
        # Slow (direct) evaluation
        slow = [polynomial.eval(x) for x in xs]
        
        self.assertEqual(fast, slow)

if __name__ == '__main__':
    unittest.main()