from typing import List, Tuple, Optional, Iterator
from dataclasses import dataclass
from py_ecc.bls12_381 import FQ, field_modulus

# Scalar equivalent en Python
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
        return Scalar(self.value + other.value)
    
    def __sub__(self, other: 'Scalar') -> 'Scalar':
        return Scalar(self.value - other.value)
    
    def __mul__(self, other: 'Scalar') -> 'Scalar':
        return Scalar(self.value * other.value)
    
    def __eq__(self, other: 'Scalar') -> bool:
        return self.value == other.value
    
    def invert(self) -> Optional['Scalar']:
        # Implémentation de l'inversion modulaire avec l'algorithme d'Euclide étendu
        def extended_euclidean(a: int, b: int) -> Tuple[int, int, int]:
            if a == 0:
                return b, 0, 1
            gcd, x1, y1 = extended_euclidean(b % a, a)
            x = y1 - (b // a) * x1
            y = x1
            return gcd, x, y
            
        if self.value == 0:
            return None
            
        _, x, _ = extended_euclidean(self.value, field_modulus)
        return Scalar(x % field_modulus)

@dataclass
class Polynomial:
    degree: int
    coeffs: List[Scalar]
    
    def __eq__(self, other: 'Polynomial') -> bool:
        if self.degree != other.degree:
            return False
        return all(l == r for l, r in zip(self.coeffs, other.coeffs))
    
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
            if i == 0:
                return 0
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
    
    def coeffs_vec(self) -> List[Scalar]:
        coeffs = self.coeffs[:self.num_coeffs()]
        return coeffs
    
    def iter_coeffs(self) -> Iterator[Scalar]:
        return iter(self.coeffs[:self.num_coeffs()])
    
    def eval(self, x: Scalar) -> Scalar:
        res = self.coeffs[self.degree()]
        
        for i in range(self.degree() - 1, -1, -1):
            res = res * x + self.coeffs[i]
            
        return res
    
    def best_mul(self, other: 'Polynomial') -> 'Polynomial':
        return self * other
    
    def __mul__(self, other: 'Polynomial') -> 'Polynomial':
        result = Polynomial.new_zero_with_size(self.degree() + other.degree() + 1)
        
        for i in range(self.num_coeffs()):
            for j in range(other.num_coeffs()):
                result.coeffs[i + j] = result.coeffs[i + j] + (self.coeffs[i] * other.coeffs[j])
        
        result.degree = self.degree() + other.degree()
        return result
    
    def long_division(self, divisor: 'Polynomial') -> Tuple['Polynomial', Optional['Polynomial']]:
        if self.is_zero():
            return (Polynomial.new_zero(), None)
        elif divisor.is_zero():
            raise ValueError("divisor must not be zero!")
        elif self.degree < divisor.degree():
            return (Polynomial.new_zero(), Some(self.clone()))
        else:
            remainder = self.clone()
            quotient = Polynomial.new_from_coeffs(
                [Scalar.zero()] * (self.degree() - divisor.degree() + 1),
                self.degree() - divisor.degree()
            )
            
            lead_inverse = divisor.lead().invert()
            if lead_inverse is None:
                raise ValueError("Failed to compute inverse of leading coefficient")
                
            while not remainder.is_zero() and remainder.degree() >= divisor.degree():
                factor = remainder.lead() * lead_inverse
                i = remainder.degree() - divisor.degree()
                quotient.coeffs[i] = factor
                
                for j, coeff in enumerate(divisor.iter_coeffs()):
                    remainder.coeffs[i + j] = remainder.coeffs[i + j] - (coeff * factor)
                
                remainder.shrink_degree()
            
            if remainder.is_zero():
                return (quotient, None)
            else:
                return (quotient, remainder)

    def clone(self) -> 'Polynomial':
        return Polynomial(self.degree, self.coeffs.copy())

    @staticmethod
    def lagrange_coefficients(xs: List[Scalar]) -> List[Scalar]:
        assert len(xs) > 1, "undefined for 1 point"

        tree = SubProductTree.new_from_points(xs)
        zero = Scalar.zero()
        vanishing_at_0 = tree.product.eval(zero)  # V_T(0)
        
        # V_{T \ {j}}(0) = V_T(0) / (0 - j)
        nums = []
        for j in xs:
            inv = (zero - j).invert()
            if inv is None:
                raise ValueError("Failed to compute inverse")
            nums.append(vanishing_at_0 * inv)

        m_prime = tree.product.clone()
        for i in range(1, m_prime.num_coeffs()):
            m_prime.coeffs[i] = m_prime.coeffs[i] * Scalar(i)
        
        m_prime.coeffs.pop(0)
        m_prime.degree -= 1

        cs = []
        evals = m_prime.multi_eval(xs)
        for i, c in enumerate(evals):
            inv = c.invert()
            if inv is None:
                raise ValueError("Failed to compute inverse")
            cs.append(nums[i] * inv)

        return cs

    def multi_eval(self, xs: List[Scalar]) -> List[Scalar]:
        assert len(xs) > self.degree()
        tree = SubProductTree.new_from_points(xs)
        return tree.eval(xs, self)

    def multi_eval_with_tree(self, xs: List[Scalar], tree: 'SubProductTree') -> List[Scalar]:
        assert len(xs) > self.degree()
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
            
            r0_tuple = f.long_division(self.left.product)
            r1_tuple = f.long_division(self.right.product)
            
            if r0_tuple[1] is None or r1_tuple[1] is None:
                raise ValueError("Unexpected None remainder in division")
                
            l0 = self.left.eval(xs[:mid], r0_tuple[1])
            l1 = self.right.eval(xs[mid:], r1_tuple[1])
            
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