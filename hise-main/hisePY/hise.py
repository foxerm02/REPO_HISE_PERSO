import random
from dataclasses import dataclass
from py_ecc.bls12_381 import (
    G1,
    G2,
    multiply,
    add,
    pairing,
    final_exponentiate,
    FQ,
    FQ2,
    FQ12,
)
from hashlib import sha256
from typing import List, Tuple


# Utility functions

def hash_to_scalar(data: bytes) -> int:
    """Hash data to a scalar value."""
    return int(sha256(data).hexdigest(), 16) % G1[0].field_modulus

def hash_to_g1(data: bytes) -> Tuple[FQ, FQ]:
    """Hash data to a point on G1."""
    scalar = hash_to_scalar(data)
    return multiply(G1, scalar)


def pedersen_commit(g: Tuple[FQ, FQ], h: Tuple[FQ, FQ], alpha: int, beta: int) -> Tuple[FQ, FQ]:
    """Pedersen commitment."""
    part1 = multiply(g, alpha)
    part2 = multiply(h, beta)
    return add(part1, part2)


def random_scalar() -> int:
    """Generate a random scalar."""
    return random.randint(1, G1[0].field_modulus - 1)


@dataclass
class HiseNizkProofParams:
    g: Tuple[FQ, FQ]
    h: Tuple[FQ, FQ]

    @staticmethod
    def new():
        g = G1
        while True:
            r = random_scalar()
            if r != 0:
                h = multiply(g, r)
                return HiseNizkProofParams(g, h)


@dataclass
class HiseNizkWitness:
    alpha1: int
    alpha2: int
    beta1: int
    beta2: int


@dataclass
class HiseEncNizkStatement:
    g: Tuple[FQ, FQ]
    h: Tuple[FQ, FQ]
    h_of_x_eps: Tuple[FQ, FQ]
    h_of_x_eps_pow_a: Tuple[FQ, FQ]
    com: Tuple[FQ, FQ]


@dataclass
class HiseEncNizkProof:
    ut1: Tuple[FQ, FQ]
    ut2: Tuple[FQ, FQ]
    alpha_z1: int
    alpha_z2: int


class Hise:
    @staticmethod
    def setup(n: int, t: int):
        pp = HiseNizkProofParams.new()

        def random_poly(degree):
            return [random_scalar() for _ in range(degree + 1)]

        p1 = random_poly(t - 1)
        p2 = random_poly(t - 1)
        p3 = random_poly(t - 1)
        p4 = random_poly(t - 1)

        def eval_poly(poly, x):
            result = 0
            for coeff in reversed(poly):
                result = (result * x + coeff) % G1[0].field_modulus
            return result

        private_keys = []
        commitments = []

        for i in range(1, n + 1):
            x = i
            alpha1 = eval_poly(p1, x)
            alpha2 = eval_poly(p2, x)
            beta1 = eval_poly(p3, x)
            beta2 = eval_poly(p4, x)

            witness = HiseNizkWitness(alpha1, alpha2, beta1, beta2)
            private_keys.append(witness)

            com_alpha = pedersen_commit(pp.g, pp.h, alpha1, alpha2)
            com_beta = pedersen_commit(pp.g, pp.h, beta1, beta2)
            commitments.append((com_alpha, com_beta))

        return pp, private_keys, commitments

    @staticmethod
    def encrypt_server(pp: HiseNizkProofParams, key: HiseNizkWitness, gamma: bytes):
        h_of_gamma = hash_to_g1(gamma)
        h_of_gamma_pow_alpha1 = multiply(h_of_gamma, key.alpha1)

        stmt = HiseEncNizkStatement(
            g=pp.g,
            h=pp.h,
            h_of_x_eps=h_of_gamma,
            h_of_x_eps_pow_a=h_of_gamma_pow_alpha1,
            com=multiply(pp.g, key.alpha1),
        )

        proof = HiseEncNizkProof(
            ut1=h_of_gamma_pow_alpha1,
            ut2=multiply(pp.g, key.alpha1),
            alpha_z1=key.alpha1,
            alpha_z2=key.alpha2,
        )
        return stmt, proof

    @staticmethod
    def encrypt_client_phase_1():
        return bytes(random.getrandbits(8) for _ in range(32))

    @staticmethod
    def encrypt_client_phase_2(m: int, server_responses):
        for stmt, proof in server_responses:
            assert stmt and proof

        n = len(server_responses)
        all_xs = [i + 1 for i in range(n)]
        coeffs = [1 for _ in range(n)]  # Placeholder for Lagrange coefficients

        solo_evals = [stmt.h_of_x_eps_pow_a for stmt, _ in server_responses]
        gk = G1
        for eval, coeff in zip(solo_evals, coeffs):
            gk = add(gk, multiply(eval, coeff))

        log_m = int((m).bit_length())

        for _ in range(m):
            r_i = random_scalar()
            g1_pow_r_i = multiply(G2, r_i)
            for _ in range(log_m):
                x_w_j = Hise.encrypt_client_phase_1()
                h_of_x_w_j = hash_to_g1(x_w_j)
                h_of_x_w_j_pow_r_i = multiply(h_of_x_w_j, r_i)

            mk_j = pairing(gk, g1_pow_r_i)
        return mk_j

    @staticmethod
    def decrypt_client_phase_1():
        x_eps = bytes(random.getrandbits(8) for _ in range(32))
        x_w = bytes(random.getrandbits(8) for _ in range(32))
        return x_eps, x_w

    @staticmethod
    def decrypt_client_phase_2(m: int, server_responses):
        for stmt, proof in server_responses:
            assert stmt and proof

        n = len(server_responses)
        all_xs = [i + 1 for i in range(n)]
        coeffs = [1 for _ in range(n)]  # Placeholder for Lagrange coefficients

        solo_evals = [stmt.h_of_x_eps_pow_a for stmt, _ in server_responses]
        gk = G1
        for eval, coeff in zip(solo_evals, coeffs):
            gk = add(gk, multiply(eval, coeff))

        R = multiply(G2, random_scalar())
        S_w = multiply(G2, random_scalar())
        g_B = server_responses[0][0].com

        for _ in range(m):
            e_r_z = pairing(gk, R)
            e_g_B_s_w = pairing(g_B, S_w)
            decrypted_result = final_exponentiate(add(e_r_z, -e_g_B_s_w))
        return decrypted_result


if __name__ == "__main__":
    n, t = 3, 2
    pp, keys, commitments = Hise.setup(n, t)
    gamma = Hise.encrypt_client_phase_1()

    server_responses = [
        Hise.encrypt_server(pp, key, gamma) for key in keys
    ]
    Hise.encrypt_client_phase_2(1, server_responses)
