/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

namespace MetaMathlibExt

section

variable {R : Type*} [CommRing R] (a : ℕ → R)

/-- The Hessenberg–Toeplitz matrix: `a (i + 1 - j)` on and below the first
superdiagonal, `0` above it. -/
private def tH (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (j : ℕ) ≤ (i : ℕ) + 1 then a ((i : ℕ) + 1 - (j : ℕ)) else 0

/-- The signed sum over ordered compositions of `n`. -/
private def cS (n : ℕ) : R :=
  Finset.univ.sum (fun c : Composition n =>
    (-a 0) ^ (n - c.length) *
      Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r)))

private lemma comp_length_le {n : ℕ} (c : Composition n) : c.length ≤ n := by
  have h := List.length_le_sum_of_one_le c.blocks (fun i hi => c.blocks_pos hi)
  rwa [c.blocks_sum] at h

/-- Forward map for `splitEquiv`: values `< iv` go left, the rest go right. -/
private def splitTo (N iv : ℕ) (r : Fin N) : Fin iv ⊕ Fin (N - iv) :=
  if hr : r.val < iv then Sum.inl ⟨r.val, hr⟩
  else Sum.inr ⟨r.val - iv, by have h1 := r.isLt; omega⟩

/-- Backward map for `splitEquiv`. -/
private def splitInv (N iv : ℕ) (h : iv ≤ N) : Fin iv ⊕ Fin (N - iv) → Fin N :=
  Sum.elim (fun r => ⟨r.val, by have h1 := r.isLt; omega⟩)
    (fun r => ⟨r.val + iv, by have h1 := r.isLt; omega⟩)

/-- Splitting `Fin N` into values `< iv` and values `≥ iv`. -/
private def splitEquiv (N iv : ℕ) (h : iv ≤ N) : Fin N ≃ Fin iv ⊕ Fin (N - iv) where
  toFun := splitTo N iv
  invFun := splitInv N iv h
  left_inv := fun r => by
    simp only [splitTo]
    split
    · next hr =>
      have e : splitInv N iv h (Sum.inl ⟨r.val, hr⟩)
          = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e]
    · next hr =>
      have e : splitInv N iv h (Sum.inr ⟨r.val - iv, by have h1 := r.isLt; omega⟩)
          = (⟨r.val - iv + iv, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e]
      ext
      dsimp only
      omega
  right_inv := fun x => by
    rcases x with r | c
    · have e1 : splitInv N iv h (Sum.inl r)
          = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e1]
      simp only [splitTo, dite_eq_left r.isLt]
    · have e2 : splitInv N iv h (Sum.inr c)
          = (⟨c.val + iv, by have h1 := c.isLt; omega⟩ : Fin N) := rfl
      rw [e2]
      simp only [splitTo, dite_eq_right (show ¬ c.val + iv < iv by omega)]
      congr 1
      ext
      dsimp only
      omega

private lemma splitEquiv_symm_inl {N iv : ℕ} (h : iv ≤ N) (r : Fin iv) :
    (splitEquiv N iv h).symm (Sum.inl r)
      = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) := rfl

private lemma splitEquiv_symm_inr {N iv : ℕ} (h : iv ≤ N) (c : Fin (N - iv)) :
    (splitEquiv N iv h).symm (Sum.inr c)
      = (⟨c.val + iv, by have h1 := c.isLt; omega⟩ : Fin N) := rfl

private lemma succAbove_val_lt {N : ℕ} (i : Fin (N + 1)) {rv : ℕ} (hrv : rv < N)
    (hr : rv < i.val) : (i.succAbove (⟨rv, hrv⟩ : Fin N)).val = rv := by
  have hlt : (⟨rv, hrv⟩ : Fin N).castSucc < i := by
    rw [Fin.lt_def]
    change rv < i.val
    exact hr
  unfold Fin.succAbove
  rw [ite_eq_left hlt, Fin.val_castSucc]

private lemma succAbove_val_ge {N : ℕ} (i : Fin (N + 1)) {rv : ℕ} (hrv : rv < N)
    (hr : i.val ≤ rv) : (i.succAbove (⟨rv, hrv⟩ : Fin N)).val = rv + 1 := by
  have hlt : ¬ (⟨rv, hrv⟩ : Fin N).castSucc < i := by
    rw [Fin.lt_def]
    change ¬ rv < i.val
    omega
  unfold Fin.succAbove
  rw [ite_eq_right hlt, Fin.val_succ]

/-- Forward map: a composition of `n + 1` gives its first block and the rest. -/
private def compConsTo (n : ℕ) (c : Composition (n + 1))
    : Σ _i : Fin (n + 1), Composition (n - _i.val) :=
  have hne : c.blocks ≠ [] := by
    intro hcon
    have hs := c.blocks_sum
    rw [hcon] at hs
    simp at hs
  have hpos : 0 < c.blocks.head hne := c.blocks_pos (List.head_mem hne)
  have hsum : c.blocks.head hne + c.blocks.tail.sum = n + 1 := by
    have hs := c.blocks_sum
    rw [← List.cons_head_tail hne, List.sum_cons] at hs
    exact hs
  ⟨⟨c.blocks.head hne - 1, by omega⟩,
    ⟨c.blocks.tail,
      fun {i} hi => c.blocks_pos (by
        rw [← List.cons_head_tail hne]
        exact List.mem_cons_of_mem _ hi),
      by
        change c.blocks.tail.sum = n - (c.blocks.head hne - 1)
        omega⟩⟩

/-- Backward map: prepend a first block to a composition. -/
private def compConsInv (n : ℕ) (x : Σ _i : Fin (n + 1), Composition (n - _i.val))
    : Composition (n + 1) :=
  ⟨(x.1.val + 1) :: x.2.blocks,
    fun {i} hi => by
      rcases List.mem_cons.mp hi with rfl | hm
      · omega
      · exact x.2.blocks_pos hm,
    by
      have hs := x.2.blocks_sum
      have hlt := x.1.isLt
      rw [List.sum_cons]
      omega⟩

/-- A composition of `n + 1` is a first block together with a composition of
the rest. -/
private def compCons (n : ℕ) :
    Composition (n + 1) ≃ Σ _i : Fin (n + 1), Composition (n - _i.val) where
  toFun := compConsTo n
  invFun := compConsInv n
  left_inv := fun c => by
    have hne : c.blocks ≠ [] := by
      intro hcon
      have hs := c.blocks_sum
      rw [hcon] at hs
      simp at hs
    have hpos : 0 < c.blocks.head hne := c.blocks_pos (List.head_mem hne)
    apply Composition.ext
    simp only [compConsTo, compConsInv]
    rw [Nat.sub_add_cancel hpos, List.cons_head_tail hne]
  right_inv := fun x => by
    obtain ⟨i, d⟩ := x
    have h1 : (compConsTo n (compConsInv n ⟨i, d⟩)).1 = i := by
      simp only [compConsTo, compConsInv]
      exact Fin.ext (Nat.add_sub_cancel _ _)
    have h2 : (compConsTo n (compConsInv n ⟨i, d⟩)).2 ≍ d := by
      simp only [compConsTo, compConsInv]
      exact HEq.rfl
    exact Sigma.ext h1 h2

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

/-- Entries of the reindexed minor, top-left block. -/
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

/-- Entries of the reindexed minor, top-right block: all zero. -/
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

/-- Entries of the reindexed minor, bottom-right block: the smaller matrix. -/
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

/-- The minor deleting row `i` and column `0` factors as `(a 0)^i * D (N - i)`. -/
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
    rcases x with r | r <;> rcases y with c | c
    · rfl
    · change (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
          ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inr c) = 0
      have h := minor_inl_inr a N i r c
      have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt) = splitEquiv N i.val hiv :=
        rfl
      rw [he] at h
      exact h
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
    rw [he, ite_eq_right (by omega)] at h
    exact h
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
      rw [hsub] at h
      exact h
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
    rw [he] at h
    exact h
  rw [hA, hD]

/-- Determinant recurrence from expansion along the first column. -/
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
  rw [hU, Finset.sum_singleton]
  exact hterm.symm

private lemma step (N : ℕ) (IH : ∀ m, m ≤ N → (tH a m).det = cS a m) :
    (tH a (N + 1)).det = cS a (N + 1) := by
  rw [det_succ a N, cS_succ a N]
  apply Finset.sum_congr rfl
  intro i _
  rw [IH (N - i.val) (Nat.sub_le _ _)]

end

/-- `Matrix.det_toeplitzHessenberg_eq_sum_compositions` without the hypotheses
`0 < n` and `a 0 ≠ 0`; the formula holds for every `n` and every `a`. -/
theorem Matrix.det_toeplitzHessenberg_eq_sum_compositions_general {R : Type*}
    [CommRing R] (n : Nat) (a : Nat → R) :
    Matrix.det (fun i j : Fin n =>
      if (j : Nat) ≤ (i : Nat) + 1 then a ((i : Nat) + 1 - (j : Nat)) else 0) =
    Finset.univ.sum (fun c : Composition n =>
      (-a 0) ^ (n - c.length) *
        Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r))) := by
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
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact base0 a
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
        exact step a k (fun m' hm' => IH m' (by omega))
  exact hall n n le_rfl

set_option linter.unusedVariables false in
/-- Trudi's formula for the determinant of the Hessenberg–Toeplitz matrix
  `A_n(a_0; a_1, …, a_n)` as a signed sum over ordered compositions of `n`.

  Source: Taras Goy and Mark Shattuck, *Determinants of Some
  Hessenberg-Toeplitz Matrices with Motzkin Number Entries*, Journal of Integer
  Sequences 26 (2023), Article 23.3.4, matrix display `DetHess` lines 146–155,
  Lemma `lem1` lines 157–166 with equation `Trudi` at lines 159–161 and the
  equivalent composition sum at lines 163–165,
  <https://cs.uwaterloo.ca/journals/JIS/VOL26/Shattuck/sh36.tex>.

  The multinomial partition-indexed display over `s_1 + 2 * s_2 + … + n * s_n = n`
  is a source-declared equivalent encoding of this composition sum and is not
  stated separately; Brioschi's formula is the `a_0 = 1` specialization (line 167).
Proves `Wanted` entry `Matrix.det_toeplitzHessenberg_eq_sum_compositions`.
It follows from `Matrix.det_toeplitzHessenberg_eq_sum_compositions_general`; the hypotheses `hn`
and `ha0` are unused and keep the source's shape.
-/
theorem Matrix.det_toeplitzHessenberg_eq_sum_compositions {R : Type*}
    [CommRing R] (n : Nat) (hn : 0 < n) (a : Nat → R) (ha0 : a 0 ≠ 0) :
    Matrix.det (fun i j : Fin n =>
      if (j : Nat) ≤ (i : Nat) + 1 then a ((i : Nat) + 1 - (j : Nat)) else 0) =
    Finset.univ.sum (fun c : Composition n =>
      (-a 0) ^ (n - c.length) *
        Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r))) :=
  Matrix.det_toeplitzHessenberg_eq_sum_compositions_general n a

end MetaMathlibExt
