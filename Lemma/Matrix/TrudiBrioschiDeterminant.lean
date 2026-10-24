import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
open MetaMathlibExt


namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[comp_length_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma comp_length_le {n : ℕ} (c : Composition n) : c.length ≤ n := by
  have h := List.length_le_sum_of_one_le c.blocks (fun i hi => c.blocks_pos hi)
  rwa [c.blocks_sum] at h

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[splitEquiv_symm_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma splitEquiv_symm_inl {N iv : ℕ} (h : iv ≤ N) (r : Fin iv) :
  (splitEquiv N iv h).symm (Sum.inl r)
    = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[splitEquiv_symm_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma splitEquiv_symm_inr {N iv : ℕ} (h : iv ≤ N) (c : Fin (N - iv)) :
  (splitEquiv N iv h).symm (Sum.inr c)
    = (⟨c.val + iv, by have h1 := c.isLt; omega⟩ : Fin N) :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[succAbove_val_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma succAbove_val_lt {N : ℕ} (i : Fin (N + 1)) {rv : ℕ} (hrv : rv < N)
  (hr : rv < i.val) : (i.succAbove (⟨rv, hrv⟩ : Fin N)).val = rv := by
  have hlt : (⟨rv, hrv⟩ : Fin N).castSucc < i := by
    rw [Fin.lt_def]
    change rv < i.val
    exact hr
  unfold Fin.succAbove
  rw [ite_eq_left hlt, Fin.val_castSucc]

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[succAbove_val_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma succAbove_val_ge {N : ℕ} (i : Fin (N + 1)) {rv : ℕ} (hrv : rv < N)
  (hr : i.val ≤ rv) : (i.succAbove (⟨rv, hrv⟩ : Fin N)).val = rv + 1 := by
  have hlt : ¬ (⟨rv, hrv⟩ : Fin N).castSucc < i := by
    rw [Fin.lt_def]
    change ¬ rv < i.val
    omega
  unfold Fin.succAbove
  rw [ite_eq_right hlt, Fin.val_succ]

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[cS_term_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma cS_term_cons (n : ℕ) (i : Fin (n + 1)) (d : Composition (n - i.val)) :
  (fun c : Composition (n + 1) => (-a 0) ^ ((n + 1) - c.length) *
    Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r)))
    ((compCons n).symm ⟨i, d⟩)
    = a (i.val + 1) * (-a 0) ^ i.val *
      (((-a 0) ^ ((n - i.val) - d.length)) *
        Finset.univ.prod (fun r : Fin d.length => a (d.blocksFun r))) := by
  have hprod : (∏ r : Fin (d.length + 1), a (((i.val + 1) :: d.blocks).get r))
    = a (i.val + 1) * ∏ r : Fin d.length, a (d.blocksFun r) := by
    rw [Fin.prod_univ_succ]
    refine congrArg₂ _ ?_ ?_
    · congr 1
    · apply Finset.prod_congr rfl
      intro r _
      congr 1
  have hexp : (n + 1) - (d.length + 1) = n - d.length := by omega
  have hsplit : n - d.length = i.val + ((n - i.val) - d.length) := by
    have hle := comp_length_le d
    have hlt := i.isLt
    omega
  change (-a 0) ^ ((n + 1) - (d.length + 1)) *
    (∏ r : Fin (d.length + 1), a (((i.val + 1) :: d.blocks).get r)) = _
  rw [hexp, hsplit, pow_add, hprod]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[cS_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma cS_succ (n : ℕ) :
  cS a (n + 1)
    = ∑ i : Fin (n + 1), a (i.val + 1) * (-a 0) ^ i.val * cS a (n - i.val) := by
  unfold cS
  rw [← Equiv.sum_comp (compCons n).symm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact cS_term_cons a n i d

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[minor_inl_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma minor_inl_inl (N : ℕ) (i : Fin (N + 1)) (r c : Fin i.val) :
  (Matrix.reindex (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
    (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
    ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inl c)
    = if c.val ≤ r.val then a (r.val - c.val) else 0 := by
  have hiv : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have hR : (i.succAbove (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N)).val = r.val :=
    succAbove_val_lt i _ r.isLt
  have hC : (Fin.succ (⟨c.val, by have h1 := c.isLt; omega⟩ : Fin N)).val = c.val + 1 := rfl
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitEquiv_symm_inl]
  unfold tH
  rw [hR, hC]
  by_cases h : c.val ≤ r.val
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[minor_inl_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma minor_inl_inr (N : ℕ) (i : Fin (N + 1)) (r : Fin i.val) (c : Fin (N - i.val)) :
  (Matrix.reindex (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
    (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
    ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inr c)
    = 0 := by
  have hiv : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have hR : (i.succAbove (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N)).val = r.val :=
    succAbove_val_lt i _ r.isLt
  have hC : (Fin.succ (⟨c.val + i.val, by have h1 := c.isLt; omega⟩ : Fin N)).val
    = c.val + i.val + 1 := rfl
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitEquiv_symm_inl,
    splitEquiv_symm_inr]
  unfold tH
  rw [hR, hC, ite_eq_right (by have h1 := r.isLt; omega)]

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[minor_inr_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma minor_inr_inr (N : ℕ) (i : Fin (N + 1)) (r c : Fin (N - i.val)) :
  (Matrix.reindex (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
    (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
    ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inr r) (Sum.inr c)
    = tH a (N - i.val) r c := by
  have hiv : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have hR : (i.succAbove (⟨r.val + i.val, by have h1 := r.isLt; omega⟩ : Fin N)).val
    = r.val + i.val + 1 := by
    apply succAbove_val_ge i _ _
    have h1 := r.isLt
    omega
  have hC : (Fin.succ (⟨c.val + i.val, by have h1 := c.isLt; omega⟩ : Fin N)).val
    = c.val + i.val + 1 := rfl
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitEquiv_symm_inr]
  unfold tH
  rw [hR, hC]
  by_cases h : c.val ≤ r.val + 1
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[minor_det_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma minor_det_zero (N : ℕ) (i : Fin (N + 1)) :
  ((tH a (N + 1)).submatrix i.succAbove Fin.succ).det
    = (a 0) ^ i.val * (tH a (N - i.val)).det := by
  have hiv : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  rw [← Matrix.det_reindex_self (splitEquiv N i.val hiv)]
  have hB : Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
    ((tH a (N + 1)).submatrix i.succAbove Fin.succ)
    = Matrix.fromBlocks
      (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inl r) (Sum.inl c)) 0
      (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inr r) (Sum.inl c))
      (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inr r) (Sum.inr c)) := by
    apply Matrix.ext
    intro x y
    obtain r | r <;> rcases y with c | c := x
    · rfl
    · change (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inr c) = 0
      have h := minor_inl_inr a N i r c
      have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt) = splitEquiv N i.val hiv :=
        rfl
      rwa [he] at h
    · rfl
    · rfl
  rw [hB]
  have hdet := Matrix.det_fromBlocks_zero₁₂
    (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inl r) (Sum.inl c))
    (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inr r) (Sum.inl c))
    (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inr r) (Sum.inr c))
  rw [hdet]
  set Ablk : Matrix (Fin i.val) (Fin i.val) R :=
    fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inl r) (Sum.inl c) with hAblk
  have htri : Ablk.IsLowerTriangular := by
    intro p q hpq
    have hpq' : p.val < q.val := by
      have h2 := OrderDual.toDual_lt_toDual.mp hpq
      rwa [Fin.lt_def] at h2
    change (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl p) (Sum.inl q) = 0
    have h := minor_inl_inl a N i p q
    have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt) = splitEquiv N i.val hiv :=
      rfl
    rwa [he, ite_eq_right (by omega)] at h
  have hA : Ablk.det = (a 0) ^ i.val := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    have hdiag : ∀ r : Fin i.val, Ablk r r = a 0 := by
      intro r
      change (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inl r)
        = a 0
      have h := minor_inl_inl a N i r r
      have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt)
        = splitEquiv N i.val hiv := rfl
      rw [he, ite_eq_left le_rfl] at h
      have hsub : r.val - r.val = 0 := by omega
      rwa [hsub] at h
    have hprod : (∏ r : Fin i.val, Ablk r r) = ∏ _r : Fin i.val, a 0 :=
      Finset.prod_congr rfl (fun r _ => hdiag r)
    rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hD : (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
    ((tH a (N + 1)).submatrix i.succAbove Fin.succ)
      (Sum.inr r) (Sum.inr c)) = tH a (N - i.val) := by
    apply Matrix.ext
    intro r c
    show (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inr r) (Sum.inr c)
      = tH a (N - i.val) r c
    have h := minor_inr_inr a N i r c
    have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt) = splitEquiv N i.val hiv :=
      rfl
    rwa [he] at h
  rw [hA, hD]

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[det_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma det_succ (n : ℕ) :
  (tH a (n + 1)).det
    = ∑ i : Fin (n + 1), a (i.val + 1) * (-a 0) ^ i.val * (tH a (n - i.val)).det := by
  have hexp := Matrix.det_succ_column_zero (tH a (n + 1))
  rw [hexp]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  rw [minor_det_zero a n i]
  have hM : tH a (n + 1) i 0 = a (i.val + 1) := by
    unfold tH
    have h0 : ((0 : Fin (n + 1)).val) = 0 := rfl
    rw [h0, ite_eq_left (Nat.zero_le _)]
    congr 1
  rw [hM, neg_pow]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[base0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma base0 : (tH a 0).det = cS a 0 := by
  rw [Matrix.det_fin_zero]
  set c0 : Composition 0 :=
    ⟨[], fun {i} hi => by simp at hi, rfl⟩ with hc0
  have h0 : ∀ c : Composition 0, c = c0 := by
    intro c
    apply Composition.ext
    have hlen : c.blocks.length = 0 := Nat.le_zero.mp (comp_length_le c)
    exact List.length_eq_zero_iff.mp hlen
  have hU : (Finset.univ : Finset (Composition 0)) = {c0} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_univ _, fun c _ => h0 c⟩
  have hl : c0.length = 0 := rfl
  have hterm : (-a 0) ^ (0 - c0.length) *
    Finset.univ.prod (fun r : Fin c0.length => a (c0.blocksFun r)) = 1 := by
    have hl : c0.length = 0 := rfl
    have hempty : (Finset.univ : Finset (Fin c0.length)) = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_univ, Fintype.card_fin, hl]
    rw [hempty, Finset.prod_empty, hl, Nat.sub_zero, pow_zero, one_mul]
  unfold cS
  rwa [hU, Finset.sum_singleton]

end MetaMathlibExt

namespace MetaMathlibExt

variable [CommRing R] (a : ℕ → R)
/--
[step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma step (N : ℕ) (IH : ∀ m, m ≤ N → (tH a m).det = cS a m) :
  (tH a (N + 1)).det = cS a (N + 1) := by
  rw [det_succ a N, cS_succ a N]
  apply Finset.sum_congr rfl
  intro i _
  rw [IH (N - i.val) (Nat.sub_le _ _)]
end


namespace MetaMathlibExt

/--
[Matrix.det_toeplitzHessenberg_eq_sum_compositions_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
lemma Matrix.det_toeplitzHessenberg_eq_sum_compositions_general
  [CommRing R]
  {n : Nat}
  {a : Nat → R} :
-- imply
  Matrix.det (fun i j : Fin n =>
    if (j : Nat) ≤ (i : Nat) + 1 then a ((i : Nat) + 1 - (j : Nat)) else 0) =
    Finset.univ.sum (fun c : Composition n =>
    (-a 0) ^ (n - c.length) *
    Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r))) := by
-- proof
  have hall : ∀ N m, m ≤ N → (tH a m).det = cS a m := by
    intro N
    induction N with
    | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.le_zero.mp hm
      subst hm0
      exact base0 a
    | succ N IH =>
      intro m hm
      obtain rfl | hmpos := Nat.eq_zero_or_pos m
      · exact base0 a
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
        exact step a k (fun m' hm' => IH m' (by omega))
  exact hall n n le_rfl
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Matrix.det_toeplitzHessenberg_eq_sum_compositions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
lemma Matrix.det_toeplitzHessenberg_eq_sum_compositions
  [CommRing R]
  {n : Nat}
  {a : Nat → R}
-- given
  (hn : 0 < n)
  (ha0 : a 0 ≠ 0) :
-- imply
  Matrix.det (fun i j : Fin n =>
    if (j : Nat) ≤ (i : Nat) + 1 then a ((i : Nat) + 1 - (j : Nat)) else 0) =
    Finset.univ.sum (fun c : Composition n =>
    (-a 0) ^ (n - c.length) *
    Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r))) :=
-- proof
  Matrix.det_toeplitzHessenberg_eq_sum_compositions_general n a

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
