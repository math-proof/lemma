import Mathlib
import sympy.Basic
import sympy.matrices.determinants.PermFinset


/--
[PermFinset](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/PermFinset.lean)
-/
@[path]
private lemma image_finset_card_eq
-- given
  (σ : Equiv.Perm (Fin n))
  (P : Finset (Fin n)) :
-- imply
  (PermFinset.imageFinset σ P).card = P.card := by
-- proof
  apply PermFinset.imageFinset_card σ P

/--
[PermFinset](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/PermFinset.lean)
-/
@[path]
private lemma perms_mapping_empty_of_card_ne_eq
-- given
  (P Q : Finset (Fin n))
  (h : P.card ≠ Q.card) :
-- imply
  PermFinset.permsMapping P Q = ∅ := by
-- proof
  apply PermFinset.permsMapping_empty_of_card_ne P Q h

/--
[PermFinset](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/PermFinset.lean)
-/
@[path]
private lemma submatrix_det_of_card_eq
  [CommRing R]
-- given
  (A : Matrix (Fin n) (Fin n) R)
  (P Q : Finset (Fin n))
  (h : P.card = Q.card) :
-- imply
  PermFinset.submatrixDet A P Q =
    (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det := by
-- proof
  apply PermFinset.submatrixDet_of_card_eq A P Q h

/--
[PermFinset](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/PermFinset.lean)
-/
@[path]
private lemma submatrix_det_of_card_ne_eq
  [CommRing R]
-- given
  (A : Matrix (Fin n) (Fin n) R)
  (P Q : Finset (Fin n))
  (h : P.card ≠ Q.card) :
-- imply
  PermFinset.submatrixDet A P Q = 0 := by
-- proof
  apply PermFinset.submatrixDet_of_card_ne A P Q h

/--
[PermFinset](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/PermFinset.lean)
-/
@[path]
private lemma submatrix_det_empty_eq
  [CommRing R]
-- given
  (A : Matrix (Fin n) (Fin n) R) :
-- imply
  PermFinset.submatrixDet A ∅ ∅ = 1 := by
-- proof
  apply PermFinset.submatrixDet_empty A

/--
[PermFinset](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/PermFinset.lean)
-/
@[path]
private lemma submatrix_det_eq_proof_version_eq
  [CommRing R]
-- given
  (A : Matrix (Fin n) (Fin n) R)
  (P Q : Finset (Fin n))
  (h : P.card = Q.card) :
-- imply
  PermFinset.submatrixDet A P Q =
    (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det := by
-- proof
  apply PermFinset.submatrixDet_eq_proof_version A P Q h


-- created on 2026-10-11
