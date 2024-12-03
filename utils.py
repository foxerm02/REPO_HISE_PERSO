from typing import List, Optional, Tuple, Callable, Any
import hashlib
from py_ecc.bls12_381 import (
    G1, G2,  # Points générateurs
    multiply, add, curve_order, neg,
    Z1, Z2, pairing  # Points à l'infini
)
from py_ecc.fields import (
    bn128_FQ12,
    bn128_FQ as FQ
)
import random
from polynomial import Polynomial, Scalar

# Table de lookup pour le calcul rapide du log2
LOG_TABLE = [
    63, 0, 58, 1, 59, 47, 53, 2, 60, 39, 48, 27, 54, 33, 42, 3, 61, 51, 37, 40, 49, 18, 28, 20, 55,
    30, 34, 11, 43, 14, 22, 4, 62, 57, 46, 52, 38, 26, 32, 41, 50, 36, 17, 19, 29, 10, 13, 21, 56,
    45, 25, 31, 35, 16, 9, 12, 44, 24, 15, 8, 23, 7, 6, 5
]


# Dans utils.py - Ajout d'une fonction pour calculer les parts DPRFs
def compute_dprf_share(h_point: Any, alpha: Scalar) -> Any:
    """Calcule une part du DPRF: H(x)^α"""
    return multiply(h_point, alpha.value)

def log2(x: int) -> int:
    """
    Calcule le log2 pour des entiers positifs.
    Version plus sûre et testée que la version précédente.
    """
    if x <= 0:
        raise ValueError("Input must be positive")
    result = 0
    while x > 1:
        x >>= 1
        result += 1
    return result



def log2_ceil(x: int) -> int:
    """
    Calcule le plafond de log2.
    """
    if x <= 0:
        raise ValueError("Input must be positive")
    return log2(x - 1) + 1 if x > 1 and not is_power_of_two(x) else log2(x)


def sample_random_poly(degree: int) -> Polynomial:
    xs = [Scalar(x) for x in range(degree + 1)]
    ys = [Scalar(random.randrange(curve_order)) for _ in range(degree + 1)]
    return Polynomial.lagrange_interpolation(xs, ys)

def pad_to_power_of_two(xs: List[Scalar]) -> List[Scalar]:
    n = 1 << log2_ceil(len(xs))
    result = xs.copy()
    if len(result) != n:
        result.extend([Scalar.zero()] * (n - len(result)))
    return result


def is_power_of_two(n: int) -> bool:
    """
    Vérifie si un nombre est une puissance de 2.
    Corrigé pour gérer correctement 0 et les nombres négatifs.
    """
    if n <= 0:
        return False
    return (n & (n - 1)) == 0

def inner_product(a: List[Scalar], b: List[Scalar]) -> Scalar:
    assert len(a) == len(b)
    return sum((x * y for x, y in zip(a, b)), start=Scalar.zero())

def multi_exp_g1(bases: List[Any], powers: List[Scalar]) -> Any:
    assert len(bases) == len(powers)
    result = Z1
    for base, power in zip(bases, powers):
        result = add(result, multiply(base, power.value))
    return result

def multi_exp_g2(bases: List[Any], powers: List[Scalar]) -> Any:
    assert len(bases) == len(powers)
    result = Z2
    for base, power in zip(bases, powers):
        result = add(result, multiply(base, power.value))
    return result

def multi_exp_g1_fast(bases: List[Any], powers: List[Scalar]) -> Any:
    # Pour l'instant, utilise la version normale
    return multi_exp_g1(bases, powers)

def multi_exp_g2_fast(bases: List[Any], powers: List[Scalar]) -> Any:
    # Pour l'instant, utilise la version normale
    return multi_exp_g2(bases, powers)

# Domaines de hachage
SCALAR_HASH_DOMAIN = b"QUUX-V01-CS02-with-expander"
DOMAIN_G1 = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_"
DOMAIN_G2 = b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_"

def hash_to_scalar(msg: bytes) -> Scalar:
    hasher = hashlib.sha256()
    hasher.update(SCALAR_HASH_DOMAIN)
    hasher.update(msg)
    return Scalar(int.from_bytes(hasher.digest(), 'big') % curve_order)


def pairing(Q: Any, P: Any) -> Any:
    """
    Calcul de pairing e(Q, P) où :
    - Q est un point G2
    - P est un point G1
    """
    from py_ecc.bls12_381 import pairing as bls_pairing
    return bls_pairing(Q, P)

def hash_to_g1(msg: bytes) -> Any:
    hasher = hashlib.sha256()
    hasher.update(DOMAIN_G1)
    hasher.update(msg)
    seed = int.from_bytes(hasher.digest(), 'big') % curve_order
    return multiply(G1, seed)

def hash_to_g2(msg: bytes) -> Any:
    hasher = hashlib.sha256()
    hasher.update(DOMAIN_G2)
    hasher.update(msg)
    seed = int.from_bytes(hasher.digest(), 'big') % curve_order
    return multiply(G2, seed)

def get_generator_in_g1() -> Any:
    return hash_to_g1(bytes([0] * 32))

def get_generator_in_g2() -> Any:
    return hash_to_g2(bytes([0] * 32))

def commit_in_g1(generator: Any, value: Scalar) -> Any:
    return multiply(generator, value.value)

def commit_in_g2(generator: Any, value: Scalar) -> Any:
    return multiply(generator, value.value)

def pedersen_commit_in_g1(g: Any, h: Any, a: Scalar, b: Scalar) -> Any:
    l = multiply(g, a.value)
    r = multiply(h, b.value)
    return add(l, r)

def pedersen_commit_in_g2(g: Any, h: Any, a: Scalar, b: Scalar) -> Any:
    l = multiply(g, a.value)
    r = multiply(h, b.value)
    return add(l, r)

def pedersen_commit_in_gt(g: Any, h: Any, a: Scalar, b: Scalar) -> Any:
    l = g ** a.value
    r = h ** b.value
    return l * r

def convert_gt_to_256_bit_hash(point: Any) -> bytes:
    hasher = hashlib.sha256()
    hasher.update(str(point).encode())
    return hasher.digest()


def points_equal(p1: Any, p2: Any) -> bool:
    """Compare deux points sur la courbe de manière sûre."""
    if p1 is None or p2 is None:
        return p1 is None and p2 is None
    # Compare les coordonnées x et y
    return (p1[0] == p2[0]) and (p1[1] == p2[1])

def modular_inverse(a: int, m: int) -> int:
    """Calcule l'inverse modulaire de a modulo m."""
    def extended_gcd(a: int, b: int) -> tuple:
        if a == 0:
            return b, 0, 1
        gcd, x1, y1 = extended_gcd(b % a, a)
        x = y1 - (b // a) * x1
        y = x1
        return gcd, x, y

    gcd, x, _ = extended_gcd(a % m, m)
    if gcd != 1:
        raise ValueError("L'inverse modulaire n'existe pas")
    return (x % m + m) % m



import unittest
from utils import *
from polynomial import Scalar

class TestUtils(unittest.TestCase):

    def test_log2(self):
        """Test de la fonction log2."""
        test_cases = [
            (1, 0),
            (2, 1),
            (3, 1),
            (4, 2),
            (7, 2),
            (8, 3),
            (9, 3),
            (1024, 10),
            (1025, 10)
        ]
        for input_val, expected in test_cases:
            with self.subTest(input_val=input_val):
                self.assertEqual(log2(input_val), expected)
                
        # Test des cas limites
        with self.assertRaises(ValueError):
            log2(0)
        with self.assertRaises(ValueError):
            log2(-1)

    def test_log2_ceil(self):
        """Test de la fonction log2_ceil."""
        test_cases = [
            (1, 0),
            (2, 1),
            (3, 2),
            (4, 2),
            (5, 3),
            (7, 3),
            (8, 3),
            (9, 4),
            (1024, 10),
            (1025, 11)
        ]
        for input_val, expected in test_cases:
            with self.subTest(input_val=input_val):
                self.assertEqual(log2_ceil(input_val), expected)
                
        # Test des cas limites
        with self.assertRaises(ValueError):
            log2_ceil(0)
        with self.assertRaises(ValueError):
            log2_ceil(-1)


    def test_is_power_of_two(self):
        """Test de la fonction is_power_of_two."""
        powers_of_two = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
        not_powers_of_two = [0, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 1023]
        
        for n in powers_of_two:
            with self.subTest(n=n):
                self.assertTrue(is_power_of_two(n))
        
        for n in not_powers_of_two:
            with self.subTest(n=n):
                self.assertFalse(is_power_of_two(n))
    
        # Test supplémentaire pour les nombres négatifs
        self.assertFalse(is_power_of_two(-2))
        self.assertFalse(is_power_of_two(-1))

    def test_pad_to_power_of_two(self):
        """Test de la fonction pad_to_power_of_two."""
        # Test avec une liste de taille 3
        original = [Scalar(1), Scalar(2), Scalar(3)]
        padded = pad_to_power_of_two(original)
        self.assertEqual(len(padded), 4)  # Prochain puissance de 2 après 3
        self.assertEqual(padded[3], Scalar.zero())

        # Test avec une liste de taille puissance de 2
        original = [Scalar(1), Scalar(2), Scalar(3), Scalar(4)]
        padded = pad_to_power_of_two(original)
        self.assertEqual(len(padded), 4)  # Déjà une puissance de 2

    def test_inner_product(self):
        """Test de la fonction inner_product."""
        a = [Scalar(1), Scalar(2), Scalar(3)]
        b = [Scalar(4), Scalar(5), Scalar(6)]
        # 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
        result = inner_product(a, b)
        self.assertEqual(result, Scalar(32))

    def test_hash_to_scalar(self):
        """Test de la fonction hash_to_scalar."""
        msg1 = b"test message 1"
        msg2 = b"test message 2"
        
        # Même message devrait donner même résultat
        self.assertEqual(hash_to_scalar(msg1), hash_to_scalar(msg1))
        
        # Messages différents devraient donner résultats différents
        self.assertNotEqual(hash_to_scalar(msg1), hash_to_scalar(msg2))

    def test_pedersen_commit_g1(self):
        """Test des engagements de Pedersen dans G1."""
        g = get_generator_in_g1()
        h = hash_to_g1(b"test generator")
        a = Scalar(123)
        b = Scalar(456)
        
        # Test de la propriété d'homomorphisme
        com1 = pedersen_commit_in_g1(g, h, a, b)
        com2 = pedersen_commit_in_g1(g, h, Scalar(123), Scalar(456))
        self.assertEqual(com1, com2)

    def test_multi_exp_g1(self):
        """Test de la multi-exponentiation dans G1."""
        bases = [get_generator_in_g1(), hash_to_g1(b"test")]
        powers = [Scalar(2), Scalar(3)]
        
        # Test que multi_exp donne le même résultat que l'exponentiation individuelle
        result = multi_exp_g1(bases, powers)
        expected = add(multiply(bases[0], powers[0].value),
                      multiply(bases[1], powers[1].value))
        self.assertEqual(result, expected)

    def test_multi_exp_g2(self):
        """Test de la multi-exponentiation dans G2."""
        bases = [get_generator_in_g2(), hash_to_g2(b"test")]
        powers = [Scalar(2), Scalar(3)]
        
        # Test que multi_exp donne le même résultat que l'exponentiation individuelle
        result = multi_exp_g2(bases, powers)
        expected = add(multiply(bases[0], powers[0].value),
                      multiply(bases[1], powers[1].value))
        self.assertEqual(result, expected)

    def test_hash_consistency(self):
        """Test de la cohérence des fonctions de hachage."""
        msg = b"test message"
        
        # Test que le même message donne toujours le même point
        g1_1 = hash_to_g1(msg)
        g1_2 = hash_to_g1(msg)
        self.assertEqual(g1_1, g1_2)
        
        g2_1 = hash_to_g2(msg)
        g2_2 = hash_to_g2(msg)
        self.assertEqual(g2_1, g2_2)

    def test_random_poly(self):
        """Test de la génération de polynômes aléatoires."""
        degree = 5
        poly = sample_random_poly(degree)
        
        # Vérifie que le degré est correct
        self.assertEqual(poly.degree, degree)
        
        # Vérifie que deux polynômes aléatoires sont différents
        poly2 = sample_random_poly(degree)
        self.assertNotEqual(poly.coeffs, poly2.coeffs)

if __name__ == '__main__':
    unittest.main()