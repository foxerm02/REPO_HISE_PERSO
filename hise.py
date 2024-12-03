# HISE Protocol Implementation
# ----------------------------
# This code implements the HISE (Hierarchical Identity-Based Encryption) protocol
# with Merkle tree verification and performance testing capabilities.


from typing import List, Tuple, Optional, Any, Dict
from dataclasses import dataclass
import random
from polynomial import Polynomial, Scalar
import utils

###########################################################################################################################################################################
###########################################################################################################################################################################
#################################################################### TYPE DEFINITIONS AND BASE CLASSES ####################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################

# Type alias comme en Rust
HiseWitnessCommitment = Tuple[Any, Any]  # (G1Projective, G1Projective)

@dataclass
class HiseNizkProofParams:
    g: Any  # G1Projective
    h: Any  # G1Projective

    @classmethod
    def new(cls) -> 'HiseNizkProofParams':
        g = utils.get_generator_in_g1()
        
        while True:
            r = Scalar(random.randrange(utils.curve_order))
            # avoid degenerate points
            if r != Scalar.zero():
                h = utils.multiply(g, r.value)
                return cls(g=g, h=h)


###########################################################################################################################################################################
###########################################################################################################################################################################
#################################################################### NIZK PROOF STRUCTURES ################################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################


@dataclass
class HiseEncNizkProof:
    ut1: Any
    ut2: Any
    alpha_z1: Scalar
    alpha_z2: Scalar

    @staticmethod
    def random_oracle(ut1: Any, ut2: Any) -> Scalar:
        # Utilisation des coordonnées x uniquement pour le hachage
        bytes_data = bytearray()
        bytes_data.extend(str(ut1[0]).encode())  # Coordonnée x de ut1
        bytes_data.extend(str(ut2[0]).encode())  # Coordonnée x de ut2
        return utils.hash_to_scalar(bytes_data)

    @classmethod
    def prove(cls, witness: 'HiseNizkWitness', stmt: 'HiseEncNizkStatement') -> 'HiseEncNizkProof':
        # Génération des valeurs aléatoires modulo l'ordre de la courbe
        αt1 = Scalar(random.randrange(utils.curve_order))
        αt2 = Scalar(random.randrange(utils.curve_order))

        # Calcul des commitments
        ut1 = utils.multiply(stmt.h_of_x_eps, αt1.value)
        temp1 = utils.multiply(stmt.g, αt1.value)
        temp2 = utils.multiply(stmt.h, αt2.value)
        ut2 = utils.add(temp1, temp2)

        # Génération du challenge
        c = cls.random_oracle(ut1, ut2)

        # Calcul des réponses (modulo l'ordre de la courbe)
        alpha_z1 = Scalar((αt1.value + (c.value * witness.α1.value)) % utils.curve_order)
        alpha_z2 = Scalar((αt2.value + (c.value * witness.α2.value)) % utils.curve_order)

        return cls(ut1=ut1, ut2=ut2, alpha_z1=alpha_z1, alpha_z2=alpha_z2)

    @staticmethod
    def verify(stmt: 'HiseEncNizkStatement', proof: 'HiseEncNizkProof') -> bool:
        c = HiseEncNizkProof.random_oracle(proof.ut1, proof.ut2)

        # Vérification de la première équation
        lhs1 = utils.multiply(stmt.h_of_x_eps, proof.alpha_z1.value)
        temp1 = utils.multiply(stmt.h_of_x_eps_pow_a, c.value)
        rhs1 = utils.add(proof.ut1, temp1)

        # Vérification de la deuxième équation
        temp2 = utils.multiply(stmt.g, proof.alpha_z1.value)
        temp3 = utils.multiply(stmt.h, proof.alpha_z2.value)
        lhs2 = utils.add(temp2, temp3)
        temp4 = utils.multiply(stmt.com, c.value)
        rhs2 = utils.add(proof.ut2, temp4)

        return utils.points_equal(lhs1, rhs1) and utils.points_equal(lhs2, rhs2)



@dataclass
class HiseDecNizkProof:
    ut1: Any
    ut2: Any
    ut3: Any
    alpha_z1: Scalar
    alpha_z2: Scalar
    beta_z1: Scalar
    beta_z2: Scalar

    @staticmethod
    def random_oracle(ut1: Any, ut2: Any, ut3: Any) -> Scalar:
        bytes_data = bytearray()
        # Utilisation des coordonnées x uniquement
        bytes_data.extend(str(ut1[0]).encode())
        bytes_data.extend(str(ut2[0]).encode())
        bytes_data.extend(str(ut3[0]).encode())
        return utils.hash_to_scalar(bytes_data)

    @classmethod
    def prove(cls, witness: 'HiseNizkWitness', stmt: 'HiseDecNizkStatement') -> 'HiseDecNizkProof':
        # Génération des valeurs aléatoires
        αt1 = Scalar(random.randrange(utils.curve_order))
        αt2 = Scalar(random.randrange(utils.curve_order))
        βt1 = Scalar(random.randrange(utils.curve_order))
        βt2 = Scalar(random.randrange(utils.curve_order))

        # Calcul des commitments
        ut1_part1 = utils.multiply(stmt.h_of_x_eps, αt1.value)
        ut1_part2 = utils.multiply(stmt.h_of_x_w, βt1.value)
        ut1 = utils.add(ut1_part1, ut1_part2)

        ut2_part1 = utils.multiply(stmt.g, αt1.value)
        ut2_part2 = utils.multiply(stmt.h, αt2.value)
        ut2 = utils.add(ut2_part1, ut2_part2)

        ut3_part1 = utils.multiply(stmt.g, βt1.value)
        ut3_part2 = utils.multiply(stmt.h, βt2.value)
        ut3 = utils.add(ut3_part1, ut3_part2)

        # Génération du challenge
        c = cls.random_oracle(ut1, ut2, ut3)

        # Calcul des réponses
        alpha_z1 = Scalar((αt1.value + (c.value * witness.α1.value)) % utils.curve_order)
        alpha_z2 = Scalar((αt2.value + (c.value * witness.α2.value)) % utils.curve_order)
        beta_z1 = Scalar((βt1.value + (c.value * witness.β1.value)) % utils.curve_order)
        beta_z2 = Scalar((βt2.value + (c.value * witness.β2.value)) % utils.curve_order)

        return cls(ut1=ut1, ut2=ut2, ut3=ut3,
                  alpha_z1=alpha_z1, alpha_z2=alpha_z2,
                  beta_z1=beta_z1, beta_z2=beta_z2)

    @staticmethod
    def verify(stmt: 'HiseDecNizkStatement', proof: 'HiseDecNizkProof') -> bool:
        c = HiseDecNizkProof.random_oracle(proof.ut1, proof.ut2, proof.ut3)

        # Vérification de la première équation
        lhs1_part1 = utils.multiply(stmt.h_of_x_eps, proof.alpha_z1.value)
        lhs1_part2 = utils.multiply(stmt.h_of_x_w, proof.beta_z1.value)
        lhs1 = utils.add(lhs1_part1, lhs1_part2)

        rhs1 = utils.add(
            proof.ut1,
            utils.multiply(stmt.h_of_x_eps_pow_a_h_of_x_w_pow_b, c.value)
        )

        # Vérification de la deuxième équation
        lhs2_part1 = utils.multiply(stmt.g, proof.alpha_z1.value)
        lhs2_part2 = utils.multiply(stmt.h, proof.alpha_z2.value)
        lhs2 = utils.add(lhs2_part1, lhs2_part2)

        rhs2 = utils.add(proof.ut2, utils.multiply(stmt.com_a, c.value))

        # Vérification de la troisième équation
        lhs3_part1 = utils.multiply(stmt.g, proof.beta_z1.value)
        lhs3_part2 = utils.multiply(stmt.h, proof.beta_z2.value)
        lhs3 = utils.add(lhs3_part1, lhs3_part2)

        rhs3 = utils.add(proof.ut3, utils.multiply(stmt.com_b, c.value))

        return (utils.points_equal(lhs1, rhs1) and 
                utils.points_equal(lhs2, rhs2) and 
                utils.points_equal(lhs3, rhs3))




###########################################################################################################################################################################
###########################################################################################################################################################################
#################################################################### STATEMENT AND WITNESS STRUCTURES #####################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################

@dataclass
class HiseEncNizkStatement:
    g: Any  # G1Projective
    h: Any  # G1Projective
    h_of_x_eps: Any  # G1Projective - H(x_eps)
    h_of_x_eps_pow_a: Any  # G1Projective - H(x_eps)^a
    com: Any  # G1Projective - ped com g^a.h^b

@dataclass
class HiseDecNizkStatement:
    g: Any  # G1Projective
    h: Any  # G1Projective
    h_of_x_eps: Any  # G1Projective - H(x_eps)
    h_of_x_w: Any  # G1Projective - H(x_w)
    h_of_x_eps_pow_a_h_of_x_w_pow_b: Any  # G1Projective - H(x_eps)^a.H(w)^b
    com_a: Any  # G1Projective - ped com g^a.h^b
    com_b: Any  # G1Projective

@dataclass
class HiseNizkWitness:
    α1: Scalar
    α2: Scalar
    β1: Scalar
    β2: Scalar



###########################################################################################################################################################################
###########################################################################################################################################################################
#################################################################### MERKLE TREE IMPLEMENTATION ###########################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################

class MerkleTree:
    """
    Implémentation de l'arbre de Merkle pour HISE.
    Gère la construction de l'arbre, la génération des chemins de preuve
    et leur vérification.
    """
    def __init__(self, leaves: List[bytes]):
        self.leaves = leaves
        self.nodes = self._build_tree()

    def _build_tree(self) -> Dict[int, List[bytes]]:
        """
        Construit l'arbre de Merkle niveau par niveau.
        
        Returns:
            Dict[int, List[bytes]]: Dictionnaire des niveaux de l'arbre
        """
        nodes = {0: self.leaves}
        current_level = self.leaves
        level = 0

        while len(current_level) > 1:
            level += 1
            current_level = self._build_level(current_level)
            nodes[level] = current_level

        return nodes

    def _build_level(self, prev_level: List[bytes]) -> List[bytes]:
        """
        Construit un niveau de l'arbre en hashant les paires de nœuds.
        
        Args:
            prev_level: Niveau précédent de l'arbre
            
        Returns:
            List[bytes]: Nouveau niveau construit
        """
        current_level = []
        for i in range(0, len(prev_level), 2):
            left = prev_level[i]
            right = prev_level[i + 1] if i + 1 < len(prev_level) else left
            current_level.append(self._hash_nodes(left, right))
        return current_level

    def _hash_nodes(self, left: bytes, right: bytes) -> bytes:
        """
        Hash deux nœuds ensemble.
        
        Args:
            left: Nœud gauche
            right: Nœud droit
            
        Returns:
            bytes: Hash des deux nœuds
        """
        combined = bytearray()
        combined.extend(left)
        combined.extend(right)
        return utils.hash_to_scalar(combined).value.to_bytes(32, 'big')

    def get_root(self) -> bytes:
        """Retourne la racine de l'arbre."""
        max_level = max(self.nodes.keys())
        return self.nodes[max_level][0]

    def get_path(self, index: int) -> List[bytes]:
        """
        Génère le chemin de preuve pour une feuille donnée.
        
        Args:
            index: Index de la feuille
            
        Returns:
            List[bytes]: Chemin de preuve Merkle
        """
        path = []
        for level in range(len(self.nodes) - 1):
            level_nodes = self.nodes[level]
            sibling_idx = index + 1 if index % 2 == 0 else index - 1
            if sibling_idx < len(level_nodes):
                path.append(level_nodes[sibling_idx])
            index //= 2
        return path

    @staticmethod
    def verify_path(leaf: bytes, path: List[bytes], root: bytes, leaf_index: int) -> bool:
        """
        Vérifie qu'un chemin de preuve est valide.
        
        Args:
            leaf: Feuille à vérifier
            path: Chemin de preuve
            root: Racine attendue
            leaf_index: Index de la feuille
            
        Returns:
            bool: True si le chemin est valide
        """
        current = leaf
        index = leaf_index
        
        for sibling in path:
            if index % 2 == 0:
                left, right = current, sibling
            else:
                left, right = sibling, current
                
            combined = bytearray()
            combined.extend(left)
            combined.extend(right)
            current = utils.hash_to_scalar(combined).value.to_bytes(32, 'big')
            index //= 2
        
        return current == root


###########################################################################################################################################################################
###########################################################################################################################################################################
#################################################################### HISE BATCH STRUCTURES ################################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################

@dataclass
class HISEBatch:
    """Structure pour gérer un lot de messages HISE"""
    N: int                  # Nombre de feuilles dans l'arbre
    root: bytes            # Racine de l'arbre de Merkle
    cipher_tree: List[bytes] # Arbre des messages chiffrés
    omega: List[bytes]      # Vecteurs binaires encodés
    r_values: List[Scalar]  # Valeurs r_k pour le déchiffrement
    g2_r_values: List[Any]  # Valeurs g2^r_k précalculées

@dataclass
class HISEKeys:
    """Structure pour stocker les clés et valeurs aléatoires"""
    rho_k: List[Scalar]    # Valeurs ρ_k pour chaque message
    r_k: List[Scalar]      # Valeurs r_k pour chaque message
    g2_r_k: List[Any]     # Valeurs g2^r_k précalculées



# Modification de la classe HISEBatchWithProofs pour inclure les clés batch
@dataclass
class HISEBatchWithProofs:
    """Structure pour un lot HISE avec preuves NIZK et chemins Merkle"""
    N: int
    root: bytes
    cipher_tree: List[bytes]
    omega: List[bytes]
    r_values: List[Scalar]
    g2_r_values: List[Any]
    enc_proofs: List[Tuple[HiseEncNizkStatement, HiseEncNizkProof]]
    x_w: bytes
    merkle_paths: List[List[bytes]]
    batch_keys: HISEKeys  # Ajout des clés batch


###########################################################################################################################################################################
###########################################################################################################################################################################
#################################################################### MERKLE TREE VERIFICATION ############################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################

class MerkleTreeVerifier:
    """Vérificateur pour l'arbre de Merkle dans HISE"""
    
    @staticmethod
    def verify_tree(batch: HISEBatchWithProofs, original_messages: List[bytes]) -> bool:
        """
        Vérifie l'intégrité de l'arbre de Merkle avec MTVer.
        
        Args:
            batch: Lot de messages avec preuves
            original_messages: Messages originaux pour vérification
            
        Returns:
            bool: True si l'arbre est valide
        """
        # 1. Vérification de la taille
        if not is_power_of_two(batch.N):
            return False

        # 2. Vérification des feuilles et chemins
        for i in range(len(original_messages)):
            leaf = Hise._compute_merkle_leaf(
                original_messages[i],
                batch.batch_keys.rho_k[i],
                batch.batch_keys.r_k[i]
            )
            
            path = batch.merkle_paths[i]
            if not MerkleTree.verify_path(leaf, path, batch.root, i):
                return False

        # 3. Vérification de la cohérence des niveaux
        levels = build_tree_levels(batch.merkle_paths, batch.N)
        return verify_tree_consistency(levels)

def compute_root_from_leaf(leaf: bytes, path: List[bytes], leaf_index: int) -> bytes:
    """
    Calcule la racine de l'arbre à partir d'une feuille et son chemin.
    
    Args:
        leaf: Feuille dont on veut calculer le chemin
        path: Liste des nœuds formant le chemin de preuve
        leaf_index: Position de la feuille dans l'arbre
        
    Returns:
        bytes: Racine calculée
    """
    current = leaf
    index = leaf_index
    
    for sibling in path:
        if index % 2 == 0:
            combined = current + sibling
        else:
            combined = sibling + current
        current = utils.hash_to_scalar(combined).value.to_bytes(32, 'big')
        index //= 2
        
    return current

def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def build_tree_levels(paths: List[List[bytes]], N: int) -> List[List[bytes]]:
    """
    Reconstruit les niveaux de l'arbre à partir des chemins.
    
    Args:
        paths: Liste des chemins de preuve
        N: Taille totale de l'arbre
    
    Returns:
        List[List[bytes]]: Niveaux reconstruits de l'arbre
    """
    if not paths:
        return []
        
    height = len(paths[0])
    levels = [[] for _ in range(height + 1)]
    
    # Placement des feuilles connues
    for i in range(len(paths)):
        levels[0].append((i, paths[i][0]))
        
    # Reconstruction des niveaux supérieurs
    for level in range(1, height + 1):
        for i in range(0, len(levels[level-1]), 2):
            if i + 1 < len(levels[level-1]):
                left = levels[level-1][i][1]
                right = levels[level-1][i+1][1]
                parent_hash = utils.hash_to_scalar(left + right).value.to_bytes(32, 'big')
                levels[level].append((i//2, parent_hash))
                
    return levels

def verify_tree_consistency(levels: List[List[bytes]]) -> bool:
    """Vérifie la cohérence entre les niveaux de l'arbre"""
    for level_idx in range(len(levels) - 1):
        level = levels[level_idx]
        next_level = levels[level_idx + 1]
        
        for i in range(0, len(level), 2):
            if i + 1 < len(level):
                # Vérifie que le parent est correct
                left = level[i][1]
                right = level[i+1][1]
                computed_parent = utils.hash_to_scalar(left + right).value.to_bytes(32, 'big')
                
                parent_idx = i // 2
                if parent_idx >= len(next_level) or next_level[parent_idx][1] != computed_parent:
                    return False
                    
    return True


###########################################################################################################################################################################
###########################################################################################################################################################################
#################################################################### MAIN HISE PROTOCOL IMPLEMENTATION ####################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################


class Hise:
    @staticmethod
    def setup(n: int, t: int) -> Tuple[HiseNizkProofParams, List[HiseNizkWitness], List[HiseWitnessCommitment]]:
        """Setup avec des polynômes séparés pour α et β"""
        pp = HiseNizkProofParams.new()
        
        # Deux polynômes séparés
        alpha_poly = utils.sample_random_poly(t - 1)  # polynôme pour α
        beta_poly = utils.sample_random_poly(t - 1)   # polynôme pour β
        
        private_keys = []
        commitments = []
        
        for i in range(1, n + 1):
            x_i = Scalar(i)
            
            # Parts séparées pour α et β
            alpha_share = alpha_poly.eval(x_i)
            beta_share = beta_poly.eval(x_i)
            
            # Randomisation séparée
            alpha_rand = Scalar(random.randrange(utils.curve_order))
            beta_rand = Scalar(random.randrange(utils.curve_order))
            
            witness = HiseNizkWitness(
                α1=alpha_share,
                α2=alpha_rand,
                β1=beta_share,
                β2=beta_rand
            )
            private_keys.append(witness)
            
            # Commitments séparés pour α et β
            com_alpha = utils.pedersen_commit_in_g1(pp.g, pp.h, alpha_share, alpha_rand)
            com_beta = utils.pedersen_commit_in_g1(pp.g, pp.h, beta_share, beta_rand)
            commitments.append((com_alpha, com_beta))
            
        return pp, private_keys, commitments
    
    @staticmethod
    def pad_messages(messages: List[bytes]) -> List[bytes]:
        """Pad la liste de messages à une puissance de 2"""
        n = len(messages)
        next_pow2 = 1 << (n - 1).bit_length()
        if n != next_pow2:
            messages.extend([b''] * (next_pow2 - n))
        return messages

    @staticmethod
    def get_random_data_commitment() -> bytes:
        """Génère un commitment aléatoire de 32 bytes."""
        return random.randbytes(32)

    @staticmethod
    def _compute_merkle_leaf(message: bytes, rho: Scalar, r: Scalar) -> bytes:
        """Calcule une feuille de l'arbre Merkle selon la construction"""
        data = bytearray()
        data.extend(message)
        data.extend(rho.value.to_bytes(32, 'big'))
        data.extend(r.value.to_bytes(32, 'big'))
        return utils.hash_to_scalar(data).value.to_bytes(32, 'big')

    @staticmethod
    def generate_batch_keys(N: int) -> HISEKeys:
        """Génère les valeurs aléatoires pour un lot"""
        g2_generator = utils.get_generator_in_g2()
        rho_k = [Scalar(random.randrange(utils.curve_order)) for _ in range(N)]
        r_k = [Scalar(random.randrange(utils.curve_order)) for _ in range(N)]
        g2_r_k = [utils.multiply(g2_generator, r.value) for r in r_k]
        return HISEKeys(rho_k=rho_k, r_k=r_k, g2_r_k=g2_r_k)
    
    @staticmethod
    def generate_merkle_paths(messages: List[bytes], merkle_tree: MerkleTree) -> List[List[bytes]]:
        """Génère les chemins de preuve pour chaque message"""
        paths = []
        for i in range(len(messages)):
            path = merkle_tree.get_path(i)
            paths.append(path)
        return paths



    @staticmethod
    def dist_gr_enc(messages: List[bytes], pp: HiseNizkProofParams, 
                    keys: List[HiseNizkWitness], coms: List[HiseWitnessCommitment], 
                    t: int) -> HISEBatchWithProofs:
        """
        Chiffre un ensemble de messages selon le protocole HISE.
        
        Args:
            messages: Liste des messages à chiffrer
            pp: Paramètres publics HISE
            keys: Liste des clés des serveurs
            coms: Liste des commitments
            t: Seuil de serveurs nécessaire
            
        Returns:
            HISEBatchWithProofs contenant les messages chiffrés et les preuves
        """
        # Initialisation et padding
        N = 1 << (len(messages) - 1).bit_length()
        padded_messages = messages + [b''] * (N - len(messages))
        batch_keys = Hise.generate_batch_keys(N)
        
        # Construction de l'arbre de Merkle
        leaves = [
            Hise._compute_merkle_leaf(msg, batch_keys.rho_k[i], batch_keys.r_k[i])
            for i, msg in enumerate(padded_messages)
        ]
        merkle_tree = MerkleTree(leaves)
        root = merkle_tree.get_root()
        merkle_paths = [merkle_tree.get_path(i) for i in range(len(messages))]
        
        # Génération de x_w et calcul des hashs
        x_w = Hise.get_random_data_commitment()
        h_root = utils.hash_to_g1(root)
        h_x_w = utils.hash_to_g1(x_w)

        # Collection des parts des serveurs et génération des preuves
        server_shares = []
        enc_proofs = []
        
        for i in range(t):
            # Calcul des parts α et β
            alpha_share = utils.multiply(h_root, keys[i].α1.value)
            beta_share = utils.multiply(h_x_w, keys[i].β1.value)
            combined_share = utils.add(alpha_share, beta_share)
            server_shares.append(combined_share)
            
            # Génération et vérification de la preuve
            stmt = HiseEncNizkStatement(
                g=pp.g, h=pp.h,
                h_of_x_eps=h_root,
                h_of_x_eps_pow_a=alpha_share,
                com=coms[i][0]
            )
            proof = HiseEncNizkProof.prove(keys[i], stmt)
            assert HiseEncNizkProof.verify(stmt, proof), f"Preuve invalide pour le serveur {i}"
            enc_proofs.append((stmt, proof))

        # Calcul du DPRF
        xs = [Scalar(i + 1) for i in range(t)]
        coeffs = Polynomial.lagrange_coefficients(xs)
        gk = utils.multi_exp_g1(server_shares, coeffs[:t])

        # Chiffrement des messages
        cipher_tree = []
        omega = []
        
        for k in range(N):
            omega.append(format(k, f'0{(N-1).bit_length()}b').encode())
            
            if k < len(messages):
                mk = utils.pairing(batch_keys.g2_r_k[k], gk)
                mk_bytes = utils.convert_gt_to_256_bit_hash(mk)
                cipher = bytes(a ^ b for a, b in zip(padded_messages[k].ljust(32, b'\0'), mk_bytes))
            else:
                cipher = b'\0' * 32
            cipher_tree.append(cipher)
    
        return HISEBatchWithProofs(
            N=N,
            root=root,
            cipher_tree=cipher_tree,
            omega=omega,
            r_values=batch_keys.r_k,
            g2_r_values=batch_keys.g2_r_k,
            enc_proofs=enc_proofs,
            x_w=x_w,
            merkle_paths=merkle_paths,
            batch_keys=batch_keys
        )


    @staticmethod
    def verify_merkle_proof(batch: HISEBatchWithProofs, original_messages: List[bytes]) -> bool:
        """Vérification MTVer avec les messages originaux"""
        # 1. Vérification de la taille
        if not is_power_of_two(batch.N):
            return False

        # 2. Vérification des feuilles et chemins
        for i in range(len(original_messages)):
            leaf = Hise._compute_merkle_leaf(
                original_messages[i],
                batch.batch_keys.rho_k[i],
                batch.batch_keys.r_k[i]
            )
            path = batch.merkle_paths[i]
            if not MerkleTree.verify_path(leaf, path, batch.root, i):
                return False

        return True

    @staticmethod
    def verify_batch_proofs(batch: HISEBatchWithProofs) -> bool:
        """Vérifie toutes les preuves NIZK du lot"""
        for stmt, proof in batch.enc_proofs:
            if not HiseEncNizkProof.verify(stmt, proof):
                return False
        return True


    @staticmethod
    def dist_gr_dec(batch: HISEBatchWithProofs, pp: HiseNizkProofParams, 
                    keys: List[HiseNizkWitness], coms: List[HiseWitnessCommitment],
                    t: int, original_messages: List[bytes]) -> List[bytes]:
        """
        Déchiffre un lot de messages selon le protocole HISE.
        
        Args:
            batch: Lot de messages chiffrés avec preuves
            pp: Paramètres publics HISE
            keys: Liste des clés des serveurs
            coms: Liste des commitments
            t: Seuil de serveurs nécessaire
            original_messages: Messages originaux pour vérification MTVer
            
        Returns:
            Liste des messages déchiffrés
            
        Raises:
            ValueError: Si la vérification MTVer ou les preuves échouent
        """
        # 1. Vérification MTVer
        if not Hise.verify_merkle_proof(batch, original_messages):
            raise ValueError("Vérification MTVer échouée")
            
        # 2. Vérification des preuves de chiffrement
        if not Hise.verify_batch_proofs(batch):
            raise ValueError("Vérification des preuves de chiffrement échouée")

        # 3. Préparation des hashes
        h_root = utils.hash_to_g1(batch.root)
        h_x_w = utils.hash_to_g1(batch.x_w)
        
        # 4. Collection des parts des serveurs
        server_shares = []
        for i in range(t):
            # Calcul des parts α et β
            alpha_share = utils.multiply(h_root, keys[i].α1.value)
            beta_share = utils.multiply(h_x_w, keys[i].β1.value)
            combined_share = utils.add(alpha_share, beta_share)
            
            # Vérification des preuves de déchiffrement
            dec_stmt = HiseDecNizkStatement(
                g=pp.g,
                h=pp.h,
                h_of_x_eps=h_root,
                h_of_x_w=h_x_w,
                h_of_x_eps_pow_a_h_of_x_w_pow_b=combined_share,
                com_a=coms[i][0],
                com_b=coms[i][1]
            )
            
            dec_proof = HiseDecNizkProof.prove(keys[i], dec_stmt)
            if not HiseDecNizkProof.verify(dec_stmt, dec_proof):
                raise ValueError(f"Preuve de déchiffrement invalide pour le serveur {i}")
            
            server_shares.append(combined_share)

        # 5. Calcul du DPRF
        xs = [Scalar(i + 1) for i in range(t)]
        coeffs = Polynomial.lagrange_coefficients(xs)
        gk = utils.multi_exp_g1(server_shares, coeffs[:t])

        # 6. Déchiffrement des messages valides
        decrypted_messages = []
        valid_indices = range(len(batch.cipher_tree))
        
        for i in valid_indices:
            if batch.cipher_tree[i] != b'\0' * 32:  # Skip padding
                mk = utils.pairing(batch.g2_r_values[i], gk)
                mk_bytes = utils.convert_gt_to_256_bit_hash(mk)
                
                message = bytes(a ^ b for a, b in zip(batch.cipher_tree[i], mk_bytes))
                message = message.rstrip(b'\0')
                
                if message:
                    decrypted_messages.append(message)

        return decrypted_messages



###########################################################################################################################################################################
###########################################################################################################################################################################
#################################################################### TESTING AND PERFORMANCE MEASUREMENT ##################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################


def test_hise_full():
    print("=== Test HISE complet avec MTVer ===")
    
    n = 4
    t = 3
    original_messages = [b'message1', b'message2', b'message3']
    
    print(f"\nConfiguration:")
    print(f"- Serveurs: {n}")
    print(f"- Seuil: {t}")
    print(f"- Messages: {original_messages}")
    
    try:
        # Setup
        pp, keys, coms = Hise.setup(n, t)
        
        # Chiffrement
        print("\nChiffrement...")
        batch = Hise.dist_gr_enc(original_messages, pp, keys, coms, t)
        
        # Test avec root invalide
        print("\nTest avec racine invalide:")
        invalid_batch = HISEBatchWithProofs(
            N=batch.N,
            root=b'\x00' * 32,
            cipher_tree=batch.cipher_tree,
            omega=batch.omega,
            r_values=batch.r_values,
            g2_r_values=batch.g2_r_values,
            enc_proofs=batch.enc_proofs,
            x_w=batch.x_w,
            merkle_paths=batch.merkle_paths,
            batch_keys=batch.batch_keys
        )
        
        try:
            Hise.verify_merkle_proof(invalid_batch, original_messages)
            print("❌ Erreur: batch invalide accepté")
        except:
            print("✓ Batch invalide correctement rejeté")
        
        # Déchiffrement normal
        print("\nDéchiffrement...")
        decrypted = Hise.dist_gr_dec(batch, pp, keys, coms, t, original_messages)
        decrypted = decrypted[:len(original_messages)]
        
        # Vérification finale
        print("\nRésultats:")
        for i, (orig, dec) in enumerate(zip(original_messages, decrypted)):
            print(f"Message {i+1}:")
            print(f"- Original : {orig}")
            print(f"- Déchiffré: {dec}")
            match = orig == dec
            print(f"- Match    : {'✓' if match else '✗'}")
        
        # Vérification
        success = decrypted == original_messages
        print(f"\nTest {'✓ réussi' if success else '❌ échoué'}")
        
    except Exception as e:
        print(f"\n❌ Erreur: {str(e)}")
        return False



import time

def test_enc_latency():
    """Test encryption latency for different configurations"""
    # rows = [[2,4,6,8]]  # Can be extended to [[2,4,6,8], [3,6,9,12], [4,8,12,16]]
    # message_sizes = [50, 150, 200, 250, 300, 350, 400, 450, 500, 550, 600, 650, 700, 750, 800, 850, 900, 950, 1000]

    rows = [[2,4,6,8]]
    # rows = [[2]]
    message_sizes = [50, 150, 200, 250, 300, 350, 400, 450, 500, 550, 600, 650, 700, 750, 800, 850, 900, 950, 1000]
    # message_sizes = [2,4]    

    for row in rows:
        for t in row:
            n = t  # Number of nodes equals threshold
            durations = []
            
            # Generate random messages for testing
            messages = [f"message{i}".encode() for i in range(max(message_sizes))]
            
            for m in message_sizes:
                # Setup
                pp, keys, coms = Hise.setup(n, t)
                batch = Hise.dist_gr_enc(messages[:m], pp, keys, coms, t)
                
                # Measure encryption time
                start_time = time.time()
                Hise.dist_gr_enc(messages[:m], pp, keys, coms, t)
                duration = time.time() - start_time
                
                print(f"HiSE encrypt for {t} nodes and {m} messages: {duration:.3f} seconds")
                durations.append(duration)

def test_dec_latency():
    """Test decryption latency for different configurations"""
    rows = [[2,4,6,8]]
    # rows = [[2]]
    message_sizes = [50, 150, 200, 250, 300, 350, 400, 450, 500, 550, 600, 650, 700, 750, 800, 850, 900, 950, 1000]
    # message_sizes = [2,4]

    for row in rows:
        for t in row:
            n = t
            durations = []
            
            messages = [f"message{i}".encode() for i in range(max(message_sizes))]
            
            for m in message_sizes:
                # Setup 
                pp, keys, coms = Hise.setup(n, t)
                batch = Hise.dist_gr_enc(messages[:m], pp, keys, coms, t)
                
                # Measure decryption time
                start_time = time.time()
                Hise.dist_gr_dec(batch, pp, keys, coms, t, messages[:m])
                duration = time.time() - start_time
                
                print(f"HiSE decrypt for {t} nodes and {m} messages: {duration:.3f} seconds")
                durations.append(duration)

def test_enc_throughput():
    """Test encryption throughput for different configurations"""
    num_cpu = 16  # Adjust based on your system
    rows = [[2,4,6,8]]
    # rows = [[2]]
    message_sizes = [50, 150, 200, 250, 300, 350, 400, 450, 500, 550, 600, 650, 700, 750, 800, 850, 900, 950, 1000]
    # message_sizes = [2,4]
    
    for row in rows:
        for t in row:
            n = t
            measurements = []
            
            messages = [f"message{i}".encode() for i in range(max(message_sizes))]
            
            for m in message_sizes:
                # Setup
                pp, keys, coms = Hise.setup(n, t)
                
                # Measure throughput
                start_time = time.time()
                Hise.dist_gr_enc(messages[:m], pp, keys, coms, t)
                duration = time.time() - start_time
                
                throughput = (num_cpu * m) / duration
                print(f"HiSE throughput for {t} nodes and {m} messages: {throughput:.2f} enc/sec")
                measurements.append(throughput)

def test_dec_throughput():
    """Test decryption throughput for different configurations"""
    num_cpu = 16
    rows = [[2,4,6,8]]
    # rows = [[2]]
    message_sizes = [50, 150, 200, 250, 300, 350, 400, 450, 500, 550, 600, 650, 700, 750, 800, 850, 900, 950, 1000]
    # message_sizes = [2,4]

    for row in rows:
        for t in row:
            n = t
            measurements = []
            
            messages = [f"message{i}".encode() for i in range(max(message_sizes))]
            
            for m in message_sizes:
                # Setup
                pp, keys, coms = Hise.setup(n, t)
                batch = Hise.dist_gr_enc(messages[:m], pp, keys, coms, t)
                
                # Measure throughput
                start_time = time.time()
                Hise.dist_gr_dec(batch, pp, keys, coms, t, messages[:m])
                duration = time.time() - start_time
                
                throughput = (num_cpu * m) / duration
                print(f"HiSE throughput for {t} nodes and {m} messages: {throughput:.2f} dec/sec")
                measurements.append(throughput)



###########################################################################################################################################################################
###########################################################################################################################################################################
############################################################################## MAIN EXECUTION #############################################################################
###########################################################################################################################################################################
###########################################################################################################################################################################


if __name__ == '__main__':
    # test_hise_full()

    print("\n=== Testing Encryption Latency ===")
    test_enc_latency()
    
    print("\n=== Testing Decryption Latency ===")
    test_dec_latency()
    
    print("\n=== Testing Encryption Throughput ===")
    test_enc_throughput()
    
    print("\n=== Testing Decryption Throughput ===")
    test_dec_throughput()