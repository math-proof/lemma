import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Determinant.PermFinset


section
-- ac-theorems


namespace PermFinset


/-- The image of a complement equals the complement of the image. -/
lemma imageFinset_compl {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) :
    imageFinset σ Pᶜ = (imageFinset σ P)ᶜ := by
  ext x
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_compl]
  constructor
  · intro ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    rw [← hyx] at hzx
    have heq := σ.injective hzx
    exact hy (heq ▸ hz)
  · intro hx
    use σ.symm x
    constructor
    · intro h
      apply hx
      exact ⟨σ.symm x, h, by simp⟩
    · simp
/-- The image has the same cardinality as the original set. -/
lemma imageFinset_card {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) :
    (imageFinset σ P).card = P.card := Finset.card_map _

/-- If σ maps P to Q (i.e., σ '' P = Q), then σ⁻¹ maps Q to P. -/
lemma imageFinset_inv {n : ℕ} {σ : Equiv.Perm (Fin n)} {P Q : Finset (Fin n)}
    (h : imageFinset σ P = Q) : imageFinset σ⁻¹ Q = P := by
  simp only [imageFinset] at h ⊢
  rw [← h]
  ext x
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
    rw [← hzy] at hyx
    have : σ⁻¹ (σ z) = z := σ.symm_apply_apply z
    rw [this] at hyx
    rw [← hyx]
    exact hz
  · intro hx
    refine ⟨σ x, ⟨x, hx, rfl⟩, ?_⟩
    exact σ.symm_apply_apply x

/-- If |P| ≠ |Q|, no permutation maps P to Q. -/
lemma permsMapping_empty_of_card_ne {n : ℕ} (P Q : Finset (Fin n))
    (h : P.card ≠ Q.card) : permsMapping P Q = ∅ := by
  simp only [permsMapping, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  intro σ heq
  rw [← imageFinset_card σ P, heq] at h
  exact h rfl

end PermFinset


namespace PermFinset

open Matrix Finset

variable {R : Type*} [CommRing R]

/-- When |P| = |Q|, the submatrix determinant equals the actual determinant.
    This lemma bridges the "total" definition with the "proof-requiring" style. -/
lemma submatrixDet_of_card_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card = Q.card) :
    submatrixDet A P Q = (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det := by
  simp only [submatrixDet, h, ↓reduceDIte]

/-- When |P| ≠ |Q|, the submatrix determinant is 0. -/
lemma submatrixDet_of_card_ne {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card ≠ Q.card) :
    submatrixDet A P Q = 0 := by
  simp only [submatrixDet, h, ↓reduceDIte]

/-- The submatrix determinant of the empty sets is 1. -/
@[simp]
lemma submatrixDet_empty {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    submatrixDet A ∅ ∅ = 1 := by
  simp only [submatrixDet, Finset.card_empty, ↓reduceDIte]
  exact Matrix.det_isEmpty

/-- `PermFinset.submatrixDet` equals the proof-requiring version when |P| = |Q|.
    
    Use this lemma to convert between:
    - `PermFinset.submatrixDet A P Q` (total, returns 0 when |P| ≠ |Q|)
    - `(A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin _)).det` (requires proof)
    
    This establishes the equivalence with `CauchyBinet.submatrixDet`. -/
lemma submatrixDet_eq_proof_version {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card = Q.card) :
    submatrixDet A P Q = (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det :=
  submatrixDet_of_card_eq A P Q h

end PermFinset
end


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

/--
[PermFinset](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/PermFinset.lean)
-/
@[path]
private lemma x_imageFinset_compl
  {n : ℕ}
-- given
  (σ : Equiv.Perm (Fin n))
  (P : Finset (Fin n)) :
-- imply
  PermFinset.imageFinset σ Pᶜ = (PermFinset.imageFinset σ P)ᶜ := by
-- proof
  apply PermFinset.imageFinset_compl σ P

/--
[PermFinset](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/PermFinset.lean)
-/
@[path]
private lemma x_imageFinset_inv
  {n : ℕ}
  {σ : Equiv.Perm (Fin n)}
  {P Q : Finset (Fin n)}
-- given
  (h : PermFinset.imageFinset σ P = Q) :
-- imply
  PermFinset.imageFinset σ⁻¹ Q = P := by
-- proof
  apply PermFinset.imageFinset_inv h


-- created on 2026-10-11
-- updated on 2026-10-26
