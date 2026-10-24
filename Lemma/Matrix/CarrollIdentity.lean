import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.CarrollIdentity
open Matrix
open MetaMathlibExt.CarrollIdentity


namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_card (hij : i ≠ j) :
  Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} = m := by
  have h2 : Fintype.card {k : Fin (m + 2) // k = i ∨ k = j} = 2 := by
    have hf : Function.Bijective
      (fun k : Fin 2 => (⟨![i, j] k, by fin_cases k <;> simp⟩ :
        {k : Fin (m + 2) // k = i ∨ k = j})) := by
      constructor
      · intro a b hab
        have hval : ![i, j] a = ![i, j] b := congrArg Subtype.val hab
        fin_cases a <;> fin_cases b <;> simp_all
      · rintro ⟨k, hk⟩
        obtain rfl | rfl := hk
        · exact ⟨0, Subtype.ext rfl⟩
        · exact ⟨1, Subtype.ext rfl⟩
    rw [Fintype.card_congr (Equiv.ofBijective _ hf).symm, Fintype.card_fin]
  have hT : {k : Fin (m + 2) // ¬(k = i ∨ k = j)} ≃ {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun _ => not_or)
  have hcompl := Fintype.card_subtype_compl (fun k : Fin (m + 2) => k = i ∨ k = j)
  have hTcard := Fintype.card_congr hT
  have hfin : Fintype.card (Fin (m + 2)) = m + 2 := Fintype.card_fin _
  omega

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_schur](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_schur {T K : Type*} [DecidableEq T] [Fintype T] [DecidableEq K] [Fintype K]
  (M : Matrix T T S) (B : Matrix T K S) (Rr : Matrix K T S) (E : Matrix K K S) :
  (fromBlocks M B Rr E).det * (M.det ^ (Fintype.card T - 1) * M.det ^ Fintype.card K) =
    M.det ^ Fintype.card T * (M.det • E - Rr * M.adjugate * B).det := by
  have hMN : M * M.adjugate = M.det • (1 : Matrix T T S) := Matrix.mul_adjugate M
  have hQ : fromBlocks M B Rr E * fromBlocks M.adjugate (-(M.adjugate * B)) 0 (M.det • 1) =
    fromBlocks (M.det • 1) 0 (Rr * M.adjugate) (M.det • E - Rr * M.adjugate * B) := by
    rw [fromBlocks_multiply]
    congr 1
    · rw [Matrix.mul_zero, add_zero]
      exact hMN
    · have hMB : M * (M.adjugate * B) = M.det • B := by
      rw [← Matrix.mul_assoc, hMN, Matrix.smul_mul, Matrix.one_mul]
      rw [Matrix.mul_neg, hMB, Matrix.mul_smul, Matrix.mul_one, neg_add_cancel]
    · rw [Matrix.mul_zero, add_zero]
    · rw [show Rr * -(M.adjugate * B) = -((Rr * M.adjugate) * B) from by
      rw [Matrix.mul_neg, Matrix.mul_assoc]]
      rw [show E * (M.det • 1) = M.det • E from by rw [Matrix.mul_smul, Matrix.mul_one]]
      rw [sub_eq_add_neg, add_comm]
  calc (fromBlocks M B Rr E).det * (M.det ^ (Fintype.card T - 1) * M.det ^ Fintype.card K)
    = (fromBlocks M B Rr E).det *
      ((M.adjugate).det * (M.det • (1 : Matrix K K S)).det) := by
      rw [Matrix.det_adjugate, Matrix.det_smul, Matrix.det_one, mul_one]
    _ = ((fromBlocks M B Rr E) *
      fromBlocks M.adjugate (-(M.adjugate * B)) 0 (M.det • 1)).det := by
      rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_adjugate,
        Matrix.det_smul, Matrix.det_one, mul_one]
    _ = (fromBlocks (M.det • 1) 0 (Rr * M.adjugate)
      (M.det • E - Rr * M.adjugate * B)).det := by
      rw [hQ]
    _ = M.det ^ Fintype.card T * (M.det • E - Rr * M.adjugate * B).det := by
      rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Matrix.det_one, mul_one]

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_det_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_det_pair {U V : Type*} [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V]
  (A : Matrix U U S) (e₁ e₂ : V ≃ U) :
  (A.submatrix e₁ e₂).det =
    ((Equiv.Perm.sign (e₂.trans e₁.symm) : ℤ) : S) * A.det := by
  have h : A.submatrix e₁ e₂ = (A.submatrix e₁ e₁).submatrix id (e₂.trans e₁.symm) := by
    ext a b
    simp only [Matrix.submatrix_apply, id_eq, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [h, Matrix.det_permute', Matrix.det_submatrix_equiv_self]

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_ofBijective_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_ofBijective_apply {α β : Sort*} (f : α → β) (h : Function.Bijective f)
  (a : α) : Equiv.ofBijective f h a = f a :=
  rfl

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carrollSplitEquiv_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carrollSplitEquiv_inr (p q : Fin (m + 2)) (hp : p = i ∨ p = j)
  (hq : q = i ∨ q = j) (hqp : q ≠ p) (a : Fin (m + 1))
  (h : Fin.succAbove p a = q) :
  carrollSplitEquiv i j p q hp hq hqp a = Sum.inr 0 := by
  simp only [carrollSplitEquiv, carroll_ofBijective_apply, carrollSplit, dif_pos h]

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carrollSplitEquiv_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carrollSplitEquiv_inl (p q : Fin (m + 2)) (hp : p = i ∨ p = j)
  (hq : q = i ∨ q = j) (hqp : q ≠ p) (a : Fin (m + 1))
  (h : Fin.succAbove p a ≠ q) :
  carrollSplitEquiv i j p q hp hq hqp a =
    Sum.inl ⟨Fin.succAbove p a, by
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact absurd rfl hqp
      · exact ⟨Fin.succAbove_ne _ _, h⟩
      · exact ⟨h, Fin.succAbove_ne _ _⟩
      · exact absurd rfl hqp⟩ := by
  simp only [carrollSplitEquiv, carroll_ofBijective_apply, carrollSplit, dite_eq_right h]

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_reindex_full](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
omit [CommRing S] in
private lemma carroll_reindex_full (M : Matrix (Fin (m + 2)) (Fin (m + 2)) S) (hij : i ≠ j) :
  M.submatrix (carrollFull i j hij) (carrollFull i j hij) =
    fromBlocks (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) ![i, j])
      (M.submatrix ![i, j]
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
      (M.submatrix ![i, j] ![i, j]) := by
  ext x y
  cases x <;> cases y <;> rfl

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_single_uncancelled](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_single_uncancelled (M : Matrix (Fin (m + 2)) (Fin (m + 2)) S)
  (p q u v : Fin (m + 2))
  (hp : p = i ∨ p = j) (hq : q = i ∨ q = j)
  (hu : u = i ∨ u = j) (hv : v = i ∨ v = j)
  (hpu : u ≠ p) (hqv : v ≠ q)
  (er ec : Fin (m + 1) ≃ {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 1)
  (hrInr : ∀ a, Fin.succAbove p a = u → er a = Sum.inr 0)
  (hrInl : ∀ a (h : Fin.succAbove p a ≠ u),
    er a = Sum.inl ⟨Fin.succAbove p a, by
      rcases hp with rfl | rfl <;> rcases hu with rfl | rfl
      · exact absurd rfl hpu
      · exact ⟨Fin.succAbove_ne _ _, h⟩
      · exact ⟨h, Fin.succAbove_ne _ _⟩
      · exact absurd rfl hpu⟩)
  (hcInr : ∀ b, Fin.succAbove q b = v → ec b = Sum.inr 0)
  (hcInl : ∀ b (h : Fin.succAbove q b ≠ v),
    ec b = Sum.inl ⟨Fin.succAbove q b, by
      rcases hq with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl hqv
      · exact ⟨Fin.succAbove_ne _ _, h⟩
      · exact ⟨h, Fin.succAbove_ne _ _⟩
      · exact absurd rfl hqv⟩) :
  (M.submatrix (Fin.succAbove p) (Fin.succAbove q)).det *
    ((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
      (Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} - 1) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
        Fintype.card (Fin 1)) =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
      Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} *
      (((Equiv.Perm.sign (ec.trans er.symm) : ℤ) : S) *
        ((M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det *
          M u v -
          (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => u)
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
            (M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
            (M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              (fun _ : Fin 1 => v)) x 0))) := by
  have hFB : (fromBlocks
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) (fun _ : Fin 1 => v))
    (M.submatrix (fun _ : Fin 1 => u)
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
    (M.submatrix (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))).submatrix er ec =
    M.submatrix (Fin.succAbove p) (Fin.succAbove q) := by
    ext a b
    simp only [Matrix.submatrix_apply]
    by_cases ha : Fin.succAbove p a = u <;> by_cases hb : Fin.succAbove q b = v
    · rw [hrInr a ha, hcInr b hb, Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply,
      ha, hb]
    · rw [hrInr a ha, hcInl b hb, Matrix.fromBlocks_apply₂₁, Matrix.submatrix_apply, ha]
    · rw [hrInl a ha, hcInr b hb, Matrix.fromBlocks_apply₁₂, Matrix.submatrix_apply, hb]
    · rw [hrInl a ha, hcInl b hb, Matrix.fromBlocks_apply₁₁, Matrix.submatrix_apply]
  have hdet : (M.submatrix (Fin.succAbove p) (Fin.succAbove q)).det =
    ((Equiv.Perm.sign (ec.trans er.symm) : ℤ) : S) *
      (fromBlocks
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) (fun _ : Fin 1 => v))
        (M.submatrix (fun _ : Fin 1 => u)
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
        (M.submatrix (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))).det := by
    rw [← hFB]
    exact carroll_det_pair _ er ec
  have hschur := carroll_schur
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) (fun _ : Fin 1 => v))
    (M.submatrix (fun _ : Fin 1 => u)
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
    (M.submatrix (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
  have h11 : ((M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
    M.submatrix (fun _ : Fin 1 => u) (fun _ : Fin 1 => v) -
    M.submatrix (fun _ : Fin 1 => u)
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
      M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (fun _ : Fin 1 => v)).det =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M u v -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => u)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => v)) x 0) := by
    simp only [Matrix.det_fin_one, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.submatrix_apply, Matrix.mul_apply]
  calc (M.submatrix (Fin.succAbove p) (Fin.succAbove q)).det *
    ((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
      (Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} - 1) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
        Fintype.card (Fin 1))
    = (((Equiv.Perm.sign (ec.trans er.symm) : ℤ) : S) *
      (fromBlocks
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) (fun _ : Fin 1 => v))
        (M.submatrix (fun _ : Fin 1 => u)
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)))
        (M.submatrix (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))).det) *
      ((M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
        (Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} - 1) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
          Fintype.card (Fin 1)) := by
      rw [hdet]
    _ = (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
      Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} *
      (((Equiv.Perm.sign (ec.trans er.symm) : ℤ) : S) *
        ((M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det *
          M u v -
          (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => u)
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
            (M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
            (M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              (fun _ : Fin 1 => v)) x 0))) := by
      rw [mul_assoc, hschur, h11]
      ring

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_full_uncancelled](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_full_uncancelled (M : Matrix (Fin (m + 2)) (Fin (m + 2)) S)
  (hij : i ≠ j) :
  M.det * ((M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
    (Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} - 1) *
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
      Fintype.card (Fin 2)) =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^
      Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} *
      ((M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
        M.submatrix ![i, j] ![i, j] -
        M.submatrix ![i, j]
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
          (M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
          M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            ![i, j]).det := by
  have hdetM : (M.submatrix (carrollFull i j hij) (carrollFull i j hij)).det = M.det :=
    Matrix.det_submatrix_equiv_self _ _
  rw [carroll_reindex_full i j M hij] at hdetM
  rw [← hdetM]
  exact carroll_schur _ _ _ _

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_zero {R : Type*} [CommRing R] (C : Matrix (Fin (0 + 2)) (Fin (0 + 2)) R)
  (a b : Fin (0 + 2)) (hab : a ≠ b) :
  Matrix.det C * Matrix.det (Matrix.submatrix C
    (Subtype.val : {k : Fin (0 + 2) // k ≠ a ∧ k ≠ b} → Fin (0 + 2))
    (Subtype.val : {k : Fin (0 + 2) // k ≠ a ∧ k ≠ b} → Fin (0 + 2))) =
  Matrix.det (Matrix.submatrix C (Fin.succAbove a) (Fin.succAbove a)) *
    Matrix.det (Matrix.submatrix C (Fin.succAbove b) (Fin.succAbove b)) -
  Matrix.det (Matrix.submatrix C (Fin.succAbove a) (Fin.succAbove b)) *
    Matrix.det (Matrix.submatrix C (Fin.succAbove b) (Fin.succAbove a)) := by
  have key2 : ∀ (x u v : Fin (0 + 2)), u ≠ v → x ≠ u → x = v := by
    intro x u v huv hxu
    have hu := u.isLt
    have hv := v.isLt
    have hx := x.isLt
    have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
    have hxu' : x.val ≠ u.val := fun h => hxu (Fin.ext h)
    have hxx : x.val = v.val := by omega
    exact Fin.ext hxx
  have : IsEmpty {k : Fin (0 + 2) // k ≠ a ∧ k ≠ b} :=
    ⟨fun ⟨k, h1, h2⟩ => h2 (key2 k a b hab h1)⟩
  have hsig : Function.Bijective (![a, b] : Fin 2 → Fin (0 + 2)) := by
    constructor
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    · intro k
      by_cases hka : k = a
      · exact ⟨0, by simp only [hka, Matrix.cons_val_zero]⟩
      · exact ⟨1, by
        have hkb : k = b := key2 k a b hab hka
        simp only [hkb, Matrix.cons_val_one, Matrix.cons_val_zero]⟩
  have hC2 : Matrix.det C = C a a * C b b - C a b * C b a := by
    have e := Matrix.det_submatrix_equiv_self
      (Equiv.ofBijective (![a, b] : Fin 2 → Fin (0 + 2)) hsig) C
    rwa [Matrix.det_fin_two] at e
  have hTdet : Matrix.det (Matrix.submatrix C
    (Subtype.val : {k : Fin (0 + 2) // k ≠ a ∧ k ≠ b} → Fin (0 + 2))
    (Subtype.val : {k : Fin (0 + 2) // k ≠ a ∧ k ≠ b} → Fin (0 + 2))) = 1 :=
    Matrix.det_isEmpty
  have ea : Fin.succAbove a 0 = b := key2 _ _ _ hab (Fin.succAbove_ne a 0)
  have eb : Fin.succAbove b 0 = a := key2 _ _ _ (Ne.symm hab) (Fin.succAbove_ne b 0)
  rw [hTdet, mul_one, hC2]
  simp only [Matrix.det_fin_one, Matrix.submatrix_apply]
  rw [ea, eb]
  ring

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_domain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_domain (M : Matrix (Fin (m + 2)) (Fin (m + 2)) S) [IsDomain S]
  (hij : i ≠ j) (hm : 1 ≤ m)
  (hΔ : (M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ≠ 0) :
  M.det * (M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det =
  (M.submatrix (Fin.succAbove i) (Fin.succAbove i)).det *
    (M.submatrix (Fin.succAbove j) (Fin.succAbove j)).det -
  (M.submatrix (Fin.succAbove i) (Fin.succAbove j)).det *
    (M.submatrix (Fin.succAbove j) (Fin.succAbove i)).det := by
  have hcT : Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} = m :=
    carroll_card i j hij
  have eX1 : ∀ d : S, d ^ (m - 1) * d ^ 1 = d ^ m := by
    intro d
    rw [← pow_add, Nat.sub_add_cancel hm]
  have eXf : ∀ d : S, d ^ (m - 1) * d ^ 2 = d ^ m * d ^ 1 := by
    intro d
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hsign : ∀ σ : Equiv.Perm (Fin (m + 1)),
    Equiv.Perm.sign σ.symm = Equiv.Perm.sign σ :=
    fun σ => Equiv.Perm.sign_inv σ
  have hsign' : ∀ σ : Equiv.Perm (Fin (m + 1)),
    Equiv.Perm.sign σ⁻¹ = Equiv.Perm.sign σ :=
    fun σ => Equiv.Perm.sign_inv σ
  have s1 := carroll_single_uncancelled i j M (p := i) (q := i) (u := j) (v := j)
    (hp := Or.inl rfl) (hq := Or.inl rfl) (hu := Or.inr rfl) (hv := Or.inr rfl)
    (hpu := Ne.symm hij) (hqv := Ne.symm hij)
    (er := carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl) (Ne.symm hij))
    (ec := carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl) (Ne.symm hij))
    (hrInr := fun a h => carrollSplitEquiv_inr _ _ _ _ _ _ _ a h)
    (hrInl := fun a h => carrollSplitEquiv_inl _ _ _ _ _ _ _ a h)
    (hcInr := fun a h => carrollSplitEquiv_inr _ _ _ _ _ _ _ a h)
    (hcInl := fun a h => carrollSplitEquiv_inl _ _ _ _ _ _ _ a h)
  have s2 := carroll_single_uncancelled i j M (p := j) (q := j) (u := i) (v := i)
    (hp := Or.inr rfl) (hq := Or.inr rfl) (hu := Or.inl rfl) (hv := Or.inl rfl)
    (hpu := hij) (hqv := hij)
    (er := carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl) hij)
    (ec := carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl) hij)
    (hrInr := fun a h => carrollSplitEquiv_inr _ _ _ _ _ _ _ a h)
    (hrInl := fun a h => carrollSplitEquiv_inl _ _ _ _ _ _ _ a h)
    (hcInr := fun a h => carrollSplitEquiv_inr _ _ _ _ _ _ _ a h)
    (hcInl := fun a h => carrollSplitEquiv_inl _ _ _ _ _ _ _ a h)
  have s3 := carroll_single_uncancelled i j M (p := i) (q := j) (u := j) (v := i)
    (hp := Or.inl rfl) (hq := Or.inr rfl) (hu := Or.inr rfl) (hv := Or.inl rfl)
    (hpu := Ne.symm hij) (hqv := hij)
    (er := carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl) (Ne.symm hij))
    (ec := carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl) hij)
    (hrInr := fun a h => carrollSplitEquiv_inr _ _ _ _ _ _ _ a h)
    (hrInl := fun a h => carrollSplitEquiv_inl _ _ _ _ _ _ _ a h)
    (hcInr := fun a h => carrollSplitEquiv_inr _ _ _ _ _ _ _ a h)
    (hcInl := fun a h => carrollSplitEquiv_inl _ _ _ _ _ _ _ a h)
  have s4 := carroll_single_uncancelled i j M (p := j) (q := i) (u := i) (v := j)
    (hp := Or.inr rfl) (hq := Or.inl rfl) (hu := Or.inl rfl) (hv := Or.inr rfl)
    (hpu := hij) (hqv := Ne.symm hij)
    (er := carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl) hij)
    (ec := carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl) (Ne.symm hij))
    (hrInr := fun a h => carrollSplitEquiv_inr _ _ _ _ _ _ _ a h)
    (hrInl := fun a h => carrollSplitEquiv_inl _ _ _ _ _ _ _ a h)
    (hcInr := fun a h => carrollSplitEquiv_inr _ _ _ _ _ _ _ a h)
    (hcInl := fun a h => carrollSplitEquiv_inl _ _ _ _ _ _ _ a h)
  have f := carroll_full_uncancelled i j M hij
  rw [hcT, Fintype.card_fin] at s1 s2 s3 s4 f
  rw [eX1] at s1 s2 s3 s4
  rw [eXf] at f
  have hs1 : (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
    (Ne.symm hij)).trans
    (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl) (Ne.symm hij)).symm =
    Equiv.refl _ := by
    ext x
    simp
  have hs1one : ((Equiv.Perm.sign ((carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
    (Ne.symm hij)).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
    (Ne.symm hij)).symm) : ℤ) : S) = 1 := by
    rw [hs1, Equiv.Perm.sign_refl, Units.val_one, Int.cast_one]
  have hs2r : (carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl) hij).trans
    (carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl) hij).symm =
    Equiv.refl _ := by
    ext x
    simp
  have hs2one : ((Equiv.Perm.sign ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
    hij).trans (carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
    hij).symm) : ℤ) : S) = 1 := by
    rw [hs2r, Equiv.Perm.sign_refl, Units.val_one, Int.cast_one]
  have hso : (carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl) hij).trans
    (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl) (Ne.symm hij)).symm =
    ((carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
      (Ne.symm hij)).trans (carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
      hij).symm).symm := by
    rw [Equiv.symm_trans, Equiv.symm_symm]
  have hs34 : ((Equiv.Perm.sign ((carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
    (Ne.symm hij)).trans (carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
    hij).symm) : ℤ) : S) =
    ((Equiv.Perm.sign ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
      hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
      (Ne.symm hij)).symm) : ℤ) : S) := by
    rw [hso]
    exact congrArg (fun u : ℤˣ => ((u : ℤ) : S))
      (hsign ((carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
        (Ne.symm hij)).trans (carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
        hij).symm)).symm
  have hs2 : ((Equiv.Perm.sign ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
    hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
    (Ne.symm hij)).symm) : ℤ) : S) *
    ((Equiv.Perm.sign ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
      hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
      (Ne.symm hij)).symm) : ℤ) : S) = 1 := by
    have h2 : (Equiv.Perm.sign ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
      hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
      (Ne.symm hij)).symm)) *
      (Equiv.Perm.sign ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
        hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
        (Ne.symm hij)).symm)) = 1 := by
      have h := Equiv.Perm.sign_mul
        ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
          hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
          (Ne.symm hij)).symm)
        ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
          hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
          (Ne.symm hij)).symm)⁻¹
      rwa [mul_inv_cancel, Equiv.Perm.sign_one, hsign' _] at h
    rw [← Int.cast_mul, ← Units.val_mul, h2, Units.val_one, Int.cast_one]
  have c1 : (M.submatrix (Fin.succAbove i) (Fin.succAbove i)).det =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M j j -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => j)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => j)) x 0) := by
    have s1a := s1
    rw [hs1one, one_mul, mul_comm (_ ^ _) _] at s1a
    exact mul_right_cancel₀ (pow_ne_zero m hΔ) s1a
  have c2 : (M.submatrix (Fin.succAbove j) (Fin.succAbove j)).det =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M i i -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => i)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => i)) x 0) := by
    have s2a := s2
    rw [hs2one, one_mul, mul_comm (_ ^ _) _] at s2a
    exact mul_right_cancel₀ (pow_ne_zero m hΔ) s2a
  have c3 : (M.submatrix (Fin.succAbove i) (Fin.succAbove j)).det =
    ((Equiv.Perm.sign ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
      hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
      (Ne.symm hij)).symm) : ℤ) : S) *
      ((M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M j i -
        (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => j)
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
          (M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
          (M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            (fun _ : Fin 1 => i)) x 0)) := by
    have s3a := s3
    rw [mul_comm (_ ^ _) _] at s3a
    exact mul_right_cancel₀ (pow_ne_zero m hΔ) s3a
  have c4 : (M.submatrix (Fin.succAbove j) (Fin.succAbove i)).det =
    ((Equiv.Perm.sign ((carrollSplitEquiv i j j i (Or.inr rfl) (Or.inl rfl)
      hij).trans (carrollSplitEquiv i j i j (Or.inl rfl) (Or.inr rfl)
      (Ne.symm hij)).symm) : ℤ) : S) *
      ((M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M i j -
        (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => i)
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
          (M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
          (M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            (fun _ : Fin 1 => j)) x 0)) := by
    have s4a := s4
    rw [hs34, mul_comm (_ ^ _) _] at s4a
    exact mul_right_cancel₀ (pow_ne_zero m hΔ) s4a
  have cf : M.det * (M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det =
    ((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
      M.submatrix ![i, j] ![i, j] -
    M.submatrix ![i, j]
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
      M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        ![i, j]).det :=
    mul_right_cancel₀ (pow_ne_zero m hΔ) (by
      calc (M.det * (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det) *
          (M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^ m =
        M.det * ((M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^ m *
          (M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^ 1) := by
        ring
        _ = (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^ m *
          ((M.submatrix
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
            M.submatrix ![i, j] ![i, j] -
          M.submatrix ![i, j]
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
            (M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
            M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              ![i, j]).det := f
        _ = ((M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
          M.submatrix ![i, j] ![i, j] -
          M.submatrix ![i, j]
            (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
            (M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
            M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              ![i, j]).det *
            (M.submatrix
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
              (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det ^ m := by
          ring)
  have hS00 : ((M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
    M.submatrix ![i, j] ![i, j] -
    M.submatrix ![i, j]
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
      M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        ![i, j]) 0 0 =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M i i -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => i)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => i)) x 0) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply,
      Matrix.mul_apply, Matrix.cons_val_zero]
  have hS11 : ((M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
    M.submatrix ![i, j] ![i, j] -
    M.submatrix ![i, j]
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
      M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        ![i, j]) 1 1 =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M j j -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => j)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => j)) x 0) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply,
      Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hS01 : ((M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
    M.submatrix ![i, j] ![i, j] -
    M.submatrix ![i, j]
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
      M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        ![i, j]) 0 1 =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M i j -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => i)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => j)) x 0) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply,
      Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hS10 : ((M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
    M.submatrix ![i, j] ![i, j] -
    M.submatrix ![i, j]
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
      M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        ![i, j]) 1 0 =
    (M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M j i -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => j)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => i)) x 0) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply,
      Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hF2 : ((M.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det •
    M.submatrix ![i, j] ![i, j] -
    M.submatrix ![i, j]
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2)) *
      (M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate *
      M.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
        ![i, j]).det =
    ((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M i i -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => i)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => i)) x 0)) *
      ((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M j j -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => j)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => j)) x 0)) -
    ((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M i j -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => i)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => j)) x 0)) *
      ((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M j i -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => j)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => i)) x 0)) := by
    rw [Matrix.det_fin_two, hS00, hS11, hS01, hS10]
  rw [cf, hF2, c1, c2, c3, c4]
  linear_combination
    (((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M j i -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => j)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => i)) x 0)) *
      ((M.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).det * M i j -
      (∑ x, (∑ y, (M.submatrix (fun _ : Fin 1 => i)
        (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))) 0 y *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))).adjugate y x) *
        (M.submatrix
          (Subtype.val : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} → Fin (m + 2))
          (fun _ : Fin 1 => j)) x 0))) * hs2

end MetaMathlibExt.CarrollIdentity

namespace MetaMathlibExt.CarrollIdentity

variable {m : ℕ} [CommRing S] (i j : Fin (m + 2))
/--
[carroll_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
reduction to the generic integral matrix. -/
private lemma carroll_succ (m : ℕ) (hm : 1 ≤ m) (R : Type*) [CommRing R]
  (C : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (a b : Fin (m + 2)) (hab : a ≠ b) :
  Matrix.det C * Matrix.det (Matrix.submatrix C
    (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))) =
  Matrix.det (Matrix.submatrix C (Fin.succAbove a) (Fin.succAbove a)) *
    Matrix.det (Matrix.submatrix C (Fin.succAbove b) (Fin.succAbove b)) -
  Matrix.det (Matrix.submatrix C (Fin.succAbove a) (Fin.succAbove b)) *
    Matrix.det (Matrix.submatrix C (Fin.succAbove b) (Fin.succAbove a)) := by
  set G : Matrix (Fin (m + 2)) (Fin (m + 2))
    (MvPolynomial (Fin (m + 2) × Fin (m + 2)) ℤ) :=
    Matrix.mvPolynomialX _ _ ℤ with hG
  have hΔG : (G.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))).det ≠ 0 := by
    intro h0
    have hmap : (MvPolynomial.eval (fun p : Fin (m + 2) × Fin (m + 2) =>
      if p.1 = p.2 then (1 : ℤ) else 0)).mapMatrix
      (G.submatrix
        (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))
        (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))) =
      (1 : Matrix {k : Fin (m + 2) // k ≠ a ∧ k ≠ b}
        {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} ℤ) := by
      ext x y
      simp only [hG, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
        Matrix.mvPolynomialX_apply, MvPolynomial.eval_X, Matrix.one_apply]
      change (if x.val = y.val then (1 : ℤ) else 0) = if x = y then 1 else 0
      by_cases h : x = y
      · subst h
        simp
      · have hv : x.val ≠ y.val := fun he => h (Subtype.ext he)
        rw [ite_eq_right hv, ite_eq_right h]
    have heval : MvPolynomial.eval (fun p : Fin (m + 2) × Fin (m + 2) =>
      if p.1 = p.2 then (1 : ℤ) else 0) ((G.submatrix
      (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))
      (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))).det) = 1 := by
      rw [RingHom.map_det, hmap, Matrix.det_one]
    rw [h0, map_zero] at heval
    exact zero_ne_one heval
  have hGen := carroll_domain a b G hab hm hΔG
  set φ : MvPolynomial (Fin (m + 2) × Fin (m + 2)) ℤ →ₐ[ℤ] R :=
    MvPolynomial.aeval (fun p : Fin (m + 2) × Fin (m + 2) => C p.1 p.2) with hφ
  have hC := congrArg φ hGen
  simp only [map_mul, map_sub] at hC
  have eFull : φ G.det = C.det := by
    rw [hφ, hG, AlgHom.map_det, Matrix.mvPolynomialX_mapMatrix_aeval]
  have eD : φ (G.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))).det =
    (C.submatrix
    (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))
    (Subtype.val : {k : Fin (m + 2) // k ≠ a ∧ k ≠ b} → Fin (m + 2))).det := by
    rw [hφ, hG, AlgHom.map_det, AlgHom.mapMatrix_apply, ← Matrix.submatrix_map,
      ← AlgHom.mapMatrix_apply, Matrix.mvPolynomialX_mapMatrix_aeval]
  have eII : φ (G.submatrix (Fin.succAbove a) (Fin.succAbove a)).det =
    (C.submatrix (Fin.succAbove a) (Fin.succAbove a)).det := by
    rw [hφ, hG, AlgHom.map_det, AlgHom.mapMatrix_apply, ← Matrix.submatrix_map,
      ← AlgHom.mapMatrix_apply, Matrix.mvPolynomialX_mapMatrix_aeval]
  have eJJ : φ (G.submatrix (Fin.succAbove b) (Fin.succAbove b)).det =
    (C.submatrix (Fin.succAbove b) (Fin.succAbove b)).det := by
    rw [hφ, hG, AlgHom.map_det, AlgHom.mapMatrix_apply, ← Matrix.submatrix_map,
      ← AlgHom.mapMatrix_apply, Matrix.mvPolynomialX_mapMatrix_aeval]
  have eIJ : φ (G.submatrix (Fin.succAbove a) (Fin.succAbove b)).det =
    (C.submatrix (Fin.succAbove a) (Fin.succAbove b)).det := by
    rw [hφ, hG, AlgHom.map_det, AlgHom.mapMatrix_apply, ← Matrix.submatrix_map,
      ← AlgHom.mapMatrix_apply, Matrix.mvPolynomialX_mapMatrix_aeval]
  have eJI : φ (G.submatrix (Fin.succAbove b) (Fin.succAbove a)).det =
    (C.submatrix (Fin.succAbove b) (Fin.succAbove a)).det := by
    rw [hφ, hG, AlgHom.map_det, AlgHom.mapMatrix_apply, ← Matrix.submatrix_map,
      ← AlgHom.mapMatrix_apply, Matrix.mvPolynomialX_mapMatrix_aeval]
  rwa [eFull, eD, eII, eJJ, eIJ, eJI] at hC
end


namespace MetaMathlibExt.CarrollIdentity

/--
[carroll_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
lemma carroll_identity
  [CommRing R]
  {n : ℕ}
  {C : Matrix (Fin (n + 2)) (Fin (n + 2)) R}
  {i j : Fin (n + 2)}
-- given
  (hij : i ≠ j) :
-- imply
  Matrix.det C * Matrix.det (Matrix.submatrix C
    (Subtype.val : {k : Fin (n + 2) // k ≠ i ∧ k ≠ j} → Fin (n + 2))
    (Subtype.val : {k : Fin (n + 2) // k ≠ i ∧ k ≠ j} → Fin (n + 2))) =
    Matrix.det (Matrix.submatrix C (Fin.succAbove i) (Fin.succAbove i)) *
    Matrix.det (Matrix.submatrix C (Fin.succAbove j) (Fin.succAbove j)) -
    Matrix.det (Matrix.submatrix C (Fin.succAbove i) (Fin.succAbove j)) *
    Matrix.det (Matrix.submatrix C (Fin.succAbove j) (Fin.succAbove i)) := by
-- proof
  cases n with
  | zero => exact carroll_zero C i j hij
  | succ k => exact carroll_succ _ (by omega) R C i j hij

end MetaMathlibExt.CarrollIdentity


-- created on 2026-10-20
-- updated on 2026-10-23
