import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lemma.Matrix.DetOf.eq.PowSub__Mul
import Lemma.Matrix.Det.eq.Prod.of.All_All_Eq_0
import Lemma.Matrix.DetMulOfOfPowNegChoose.eq.MulPowProd.of.Le
import Lemma.Matrix.DetOf.eq.MulPowSProdProd.of.Le
import Lemma.Matrix.MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf
import Lemma.Matrix.MulOfPowAddOfPowNegChoose.eq.Zero
open Matrix Finset Nat
set_option maxHeartbeats 999999


private lemma pair_prod_succ
  {n : ℕ}
  {x : Fin (n + 1) → ℝ}
  {d : Fin (n + 1) → ℕ} :
  (∏ k : Fin (n + 1), ∏ ℓ : Fin (n + 1),
      if (k : ℕ) < (ℓ : ℕ) then (x ℓ - x k) ^ (d ℓ * d k) else 1) =
    (∏ k : Fin n, (x k.succ - x 0) ^ (d k.succ * d 0)) *
      (∏ k : Fin n, ∏ ℓ : Fin n,
        if (k : ℕ) < (ℓ : ℕ) then
          (x ℓ.succ - x k.succ) ^ (d ℓ.succ * d k.succ)
        else 1) := by
  rw [Fin.prod_univ_succ]
  have hrow0 :
    (∏ ℓ : Fin (n + 1),
      if (0 : ℕ) < (ℓ : ℕ) then (x ℓ - x 0) ^ (d ℓ * d 0) else 1) =
      ∏ k : Fin n, (x k.succ - x 0) ^ (d k.succ * d 0) := by
    rw [Fin.prod_univ_succ]
    simp
  have hrows :
    (∏ k : Fin n, ∏ ℓ : Fin (n + 1),
      if (k.succ : ℕ) < (ℓ : ℕ) then
        (x ℓ - x k.succ) ^ (d ℓ * d k.succ) else 1) =
      ∏ k : Fin n, ∏ ℓ : Fin n,
        if (k : ℕ) < (ℓ : ℕ) then
          (x ℓ.succ - x k.succ) ^ (d ℓ.succ * d k.succ) else 1 := by
    refine Fintype.prod_congr _ _ fun k => ?_
    rw [Fin.prod_univ_succ]
    simp
  change
    (∏ ℓ : Fin (n + 1),
      if (0 : ℕ) < (ℓ : ℕ) then (x ℓ - x 0) ^ (d ℓ * d 0) else 1) *
      (∏ k : Fin n, ∏ ℓ : Fin (n + 1),
        if (k.succ : ℕ) < (ℓ : ℕ) then
          (x ℓ - x k.succ) ^ (d ℓ * d k.succ) else 1) =
      _
  rw [hrow0, hrows]

private lemma offset_add_eq
  {n : ℕ}
  (d : Fin n → ℕ)
  (k : Fin n) :
  (∑ t ∈ Finset.Iio k, d t) + d k =
    ∑ t ∈ Finset.Iic k, d t := by
  classical
  rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self, add_comm]

private lemma offset_mono
  {n : ℕ}
  (d : Fin n → ℕ)
  {k₁ k₂ : Fin n}
  (h : (k₁ : ℕ) < (k₂ : ℕ)) :
  (∑ t ∈ Finset.Iio k₁, d t) + d k₁ ≤
    ∑ t ∈ Finset.Iio k₂, d t := by
  rw [offset_add_eq]
  refine Finset.sum_le_sum_of_subset ?_
  intro i hi
  simp only [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def] at hi ⊢
  exact Nat.lt_of_le_of_lt hi h

private lemma offset_unique
  {n : ℕ}
  (d : Fin n → ℕ)
  (a : ℕ)
  {k₁ k₂ : Fin n}
  (h1 : a ∈ Finset.Ico (∑ t ∈ Finset.Iio k₁, d t) ((∑ t ∈ Finset.Iio k₁, d t) + d k₁))
  (h2 : a ∈ Finset.Ico (∑ t ∈ Finset.Iio k₂, d t) ((∑ t ∈ Finset.Iio k₂, d t) + d k₂)) :
  k₁ = k₂ := by
  by_contra hne
  have h1' := (Finset.mem_Ico.mp h1)
  have h2' := (Finset.mem_Ico.mp h2)
  have hlt : (k₁ : ℕ) < (k₂ : ℕ) ∨ (k₂ : ℕ) < (k₁ : ℕ) :=
    Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne)
  cases hlt with
  | inl hlt =>
    have := offset_mono d hlt
    omega
  | inr hlt =>
    have := offset_mono d hlt
    omega

private lemma prod_lt_pair
  {n : ℕ}
  {x : Fin n → ℝ}
  {d : Fin n → ℕ} :
  (∏ i : Fin n, ∏ j ∈ Finset.Iio i, (x i - x j) ^ (d i * d j)) =
    (∏ k : Fin n, ∏ ℓ : Fin n,
      if (k : ℕ) < (ℓ : ℕ) then (x ℓ - x k) ^ (d ℓ * d k) else 1) := by
  classical
  have hswap :=
    Finset.prod_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun k ℓ =>
        if (k : ℕ) < (ℓ : ℕ) then (x ℓ - x k) ^ (d ℓ * d k) else (1 : ℝ))
  refine Eq.trans ?_ hswap.symm
  refine Fintype.prod_congr _ _ fun i => ?_
  change
    (∏ j ∈ Finset.Iio i, (x i - x j) ^ (d i * d j)) =
      ∏ k : Fin n, if (k : ℕ) < (i : ℕ) then (x i - x k) ^ (d i * d k) else 1
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp only [Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Fin.lt_def

/-- n-base geometric Vandermonde by induction on `n`. -/
@[path]
private lemma main
  {n m : ℕ}
  {x : Fin n → ℝ}
  {d : Fin n → ℕ}
-- given
  (h : ∑ k, d k = m) :
-- imply
  (Matrix.of fun (i j : Fin m) =>
      ∑ k : Fin n,
        if (i : ℕ) ∈ Finset.Ico (∑ t ∈ Finset.Iio k, d t)
            ((∑ t ∈ Finset.Iio k, d t) + d k) then
          (j : ℝ) ^ ((i : ℕ) - ∑ t ∈ Finset.Iio k, d t) * (x k) ^ (j : ℕ)
        else
          0).det =
    ∏ i : Fin n,
      ((x i) ^ ((d i).choose 2) *
        (∏ j ∈ Finset.Iio i, (x i - x j) ^ (d i * d j)) *
        (∏ j ∈ Finset.range (d i), (j ! : ℝ))) := by
-- proof
  have hprod :
    (∏ i : Fin n,
        (x i) ^ ((d i).choose 2) *
          (∏ j ∈ Finset.Iio i, (x i - x j) ^ (d i * d j)) *
          (∏ j ∈ Finset.range (d i), (j ! : ℝ))) =
      (∏ i : Fin n, (x i) ^ ((d i).choose 2)) *
        (∏ i : Fin n, ∏ j ∈ Finset.Iio i, (x i - x j) ^ (d i * d j)) *
        (∏ i : Fin n, ∏ j ∈ Finset.range (d i), (j ! : ℝ)) := by
    simp [mul_assoc, Finset.prod_mul_distrib]
  rw [hprod]
  clear hprod
  rw [prod_lt_pair (x := x) (d := d)]
  induction n generalizing m with
  | zero =>
    have hm0 : m = 0 := by
      simpa [eq_comm] using h
    subst hm0
    simp [Matrix.det_fin_zero]
  | succ n ih =>
    set d0 := d 0 with hd0
    set x0 := x 0 with hx0
    set d' : Fin n → ℕ := fun k => d k.succ with hd'
    set x' : Fin n → ℝ := fun k => x k.succ with hx'
    have hsum_succ : d0 + ∑ k : Fin n, d' k = m := by
      simpa [Fin.sum_univ_succ, d0, d'] using h
    have hsum' : ∑ k : Fin n, d' k = m - d0 := by omega
    have hd0le : d0 ≤ m := by omega
    set off : Fin (n + 1) → ℕ := fun k =>
      ∑ t ∈ Finset.Iio k, d t with hoff
    set off' : Fin n → ℕ := fun k =>
      ∑ t ∈ Finset.Iio k, d' t with hoff'
    have hoff0 : off 0 = 0 := by
      simp [off]
    have hoff_succ (k : Fin n) : off k.succ = d0 + off' k := by
      simp only [off, off', d', d0]
      classical
      have hset :
        Finset.Iio k.succ =
          insert (0 : Fin (n + 1)) ((Finset.Iio k).map (Fin.succEmb n)) := by
        rw [Fin.map_succEmb_Iio k]
        rw [Finset.Ioo_insert_left (Fin.succ_pos k)]
        ext i
        simp [Finset.mem_Ico, Finset.mem_Iio]
      have hnotin : (0 : Fin (n + 1)) ∉ (Finset.Iio k).map (Fin.succEmb n) := by
        simp
      rw [hset, Finset.sum_insert hnotin, Finset.sum_map]
      rfl
    set M := Matrix.of fun (i j : Fin m) =>
        ∑ k : Fin (n + 1),
          if (i : ℕ) ∈ Finset.Ico (off k) (off k + d k) then
            (j : ℝ) ^ ((i : ℕ) - off k) * (x k) ^ (j : ℕ)
          else
            0 with hM
    set M_rest := Matrix.of fun (i j : Fin (m - d0)) =>
        ∑ k : Fin n,
          if (i : ℕ) ∈ Finset.Ico (off' k) (off' k + d' k) then
            (j : ℝ) ^ ((i : ℕ) - off' k) * (x' k) ^ (j : ℕ)
          else
            0 with hM_rest
    set ε₁ : Fin d0 ⊕ Fin (m - d0) ≃ Fin m :=
      finSumFinEquiv.trans (finCongr (by omega : d0 + (m - d0) = m)) with hε₁
    set A₁ := Matrix.of fun (i : Fin d0) (j : Fin m) =>
        x0 ^ (j : ℕ) * ((j : ℝ) + 0) ^ (i : ℕ) with hA₁
    set A_rest := Matrix.of fun (i : Fin (m - d0)) (j : Fin m) =>
        ∑ k : Fin n,
          if (i : ℕ) ∈ Finset.Ico (off' k) (off' k + d' k) then
            x' k ^ (j : ℕ) * ((j : ℝ) + 0) ^ ((i : ℕ) - off' k)
          else
            0 with hA_rest
    set B₁ := Matrix.of fun (k : Fin m) (j : Fin d0) =>
        (-x0) ^ ((j : ℤ) - (k : ℕ)) * ((j : ℕ).choose k : ℝ) with hB₁
    set Bd := Matrix.of fun (i : Fin m) (j : Fin (m - d0)) =>
        (-x0) ^ ((d0 : ℤ) + (j : ℕ) - (i : ℕ)) *
          (if (j : ℕ) ≤ i then (d0.choose ((i : ℕ) - j) : ℝ) else 0) with hBd
    set T := Matrix.fromCols B₁ Bd with hT
    have hε₁1 : ∀ c : Fin m, ∀ hc : (c : ℕ) < d0, ε₁.symm c = Sum.inl ⟨c, hc⟩ := by
      intro c hc
      rw [Equiv.symm_apply_eq]
      ext
      simp [hε₁]
    have hε₁2 : ∀ c : Fin m, ∀ hc : ¬(c : ℕ) < d0, ε₁.symm c = Sum.inr ⟨c - d0, by omega⟩ := by
      intro c hc
      rw [Equiv.symm_apply_eq]
      ext
      simp [hε₁]
      omega
    have hε₁_inr : ∀ a : Fin (m - d0), (ε₁ (Sum.inr a) : ℕ) = d0 + a := by
      intro a
      simp [hε₁]
    have hε₁_inl : ∀ a : Fin d0, (ε₁ (Sum.inl a) : ℕ) = (a : ℕ) := by
      intro a
      simp [hε₁]
    have hrows : M.submatrix ε₁ id = Matrix.fromRows A₁ A_rest := by
      ext (a | a) j
      ·
        simp only [Matrix.submatrix_apply, id, Matrix.fromRows_apply_inl, hA₁, hM,
          Matrix.of_apply]
        rw [hε₁_inl a]
        have hterm :
          (∑ k : Fin (n + 1),
            if (a : ℕ) ∈ Finset.Ico (off k) (off k + d k) then
              (j : ℝ) ^ ((a : ℕ) - off k) * (x k) ^ (j : ℕ)
            else
              0) =
            (j : ℝ) ^ (a : ℕ) * x0 ^ (j : ℕ) := by
          rw [Fin.sum_univ_succ]
          have h0 : (a : ℕ) ∈ Finset.Ico (off 0) (off 0 + d 0) := by
            simp [hoff0, d0]
          rw [ite_eq_left h0, hoff0, tsub_zero, hx0]
          have hrest :
            (∑ k : Fin n,
              if (a : ℕ) ∈ Finset.Ico (off k.succ) (off k.succ + d k.succ) then
                (j : ℝ) ^ ((a : ℕ) - off k.succ) * (x k.succ) ^ (j : ℕ)
              else
                0) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            have : ¬((a : ℕ) ∈ Finset.Ico (off k.succ) (off k.succ + d k.succ)) := by
              rw [hoff_succ]
              intro hmem
              have h1 := (Finset.mem_Ico.mp hmem).1
              exact absurd (show d0 ≤ (a : ℕ) by omega)
                (Nat.not_le_of_gt (Fin.is_lt a))
            rw [ite_eq_right this]
          rw [hrest, add_zero]
        rw [hterm, mul_comm, add_zero]
      ·
        have ha := hε₁_inr a
        simp only [Matrix.submatrix_apply, id, Matrix.fromRows_apply_inr, hA_rest, hM,
          Matrix.of_apply]
        rw [ha, Fin.sum_univ_succ]
        have h0 : ¬(d0 + (a : ℕ) ∈ Finset.Ico (off 0) (off 0 + d 0)) := by
          simp [hoff0, d0]
        rw [ite_eq_right h0, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hoff_succ k]
        simp only [d', x']
        if hk : (a : ℕ) ∈ Finset.Ico (off' k) (off' k + d' k) then
          have hk' :
            d0 + (a : ℕ) ∈ Finset.Ico (d0 + off' k) (d0 + off' k + d' k) := by
            have h := Finset.mem_Ico.mp hk
            exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          rw [ite_eq_left hk', ite_eq_left hk, mul_comm, add_zero]
          congr 2
          omega
        else
          have hk' :
            ¬(d0 + (a : ℕ) ∈ Finset.Ico (d0 + off' k) (d0 + off' k + d' k)) := by
            intro hmem
            have h := Finset.mem_Ico.mp hmem
            exact hk (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          rw [ite_eq_right hk', ite_eq_right hk]
    have h5 : (M.submatrix ε₁ id) * T = (M.submatrix ε₁ ε₁) * (T.submatrix ε₁ id) := by
      rw [Matrix.submatrix_mul_equiv]
      rfl
    have hT1 : (T.submatrix ε₁ id).det = 1 := by
      rw [← Matrix.det_submatrix_equiv_self ε₁.symm, Matrix.submatrix_submatrix]
      simp only [Equiv.self_comp_symm, Function.id_comp]
      rw [Matrix.det_of_isUpperTriangular]
      ·
        refine Finset.prod_eq_one fun c _ => ?_
        simp only [Matrix.submatrix_apply, id]
        if hc : (c : ℕ) < d0 then
          rw [hε₁1 c hc, hT, Matrix.fromCols_apply_inl, hB₁, Matrix.of_apply]
          simp
        else
          rw [hε₁2 c hc, hT, Matrix.fromCols_apply_inr, hBd, Matrix.of_apply]
          have hcd : ((d0 : ℤ) + ((c - d0 : ℕ) : ℤ) - (c : ℤ)) = 0 := by
            push_cast [Nat.cast_sub (by omega : d0 ≤ (c : ℕ))]
            ring
          simp only [hcd, zpow_zero, one_mul]
          rw [ite_eq_left (by omega), show (c : ℕ) - ((c : ℕ) - d0) = d0 by omega, Nat.choose_self,
            Nat.cast_one]
      ·
        intro k c hkc
        have hkc : (c : ℕ) < k := hkc
        simp only [Matrix.submatrix_apply, id]
        if hc : (c : ℕ) < d0 then
          rw [hε₁1 c hc, hT, Matrix.fromCols_apply_inl, hB₁, Matrix.of_apply]
          simp only
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
        else
          rw [hε₁2 c hc, hT, Matrix.fromCols_apply_inr, hBd, Matrix.of_apply]
          simp only
          rw [ite_eq_left (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    have hmain := congrArg Matrix.det h5
    rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, hT1, mul_one, hrows, hT,
      Matrix.fromRows_mul_fromCols] at hmain
    have hz : A₁ * Bd = 0 := by
      simpa [hA₁, hBd, hx0] using
        MulOfPowAddOfPowNegChoose.eq.Zero (δ := (0 : ℝ)) (x := x0) (d := d0) (m := m)
    rw [hz, Matrix.det_fromBlocks_zero₁₂, hA₁, hB₁,
      DetMulOfOfPowNegChoose.eq.MulPowProd.of.Le hd0le] at hmain
    have hRestBd :
      (A_rest * Bd).det =
        (∏ k : Fin n, (x' k - x0) ^ (d' k * d0)) * M_rest.det := by
      classical
      have hoff'_le (k : Fin n) : off' k + d' k ≤ m - d0 := by
        have h1 : off' k + d' k = ∑ t ∈ Finset.Iic k, d' t := by
          simpa [off'] using offset_add_eq d' k
        rw [h1, ← hsum']
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hoff'_succ (k : Fin n) (hk : (k : ℕ) + 1 < n) :
        off' ⟨(k : ℕ) + 1, hk⟩ = off' k + d' k := by
        have hL : off' ⟨(k : ℕ) + 1, hk⟩ = ∑ t ∈ Finset.Iic k, d' t := by
          simp only [off']
          have hI :
            Finset.Iio (⟨(k : ℕ) + 1, hk⟩ : Fin n) = Finset.Iic k := by
            ext i
            simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
            exact Nat.lt_succ_iff
          rw [hI]
        have hR : off' k + d' k = ∑ t ∈ Finset.Iic k, d' t := by
          simpa [off'] using offset_add_eq d' k
        rw [hL, hR]
      have hoff'_last (k : Fin n) (hk : (k : ℕ) = n - 1) :
        off' k + d' k = m - d0 := by
        have hn : 0 < n := by
          have : (k : ℕ) < n := k.isLt
          omega
        have h1 : off' k + d' k = ∑ j : Fin n, d' j := by
          rw [show off' k + d' k = ∑ t ∈ Finset.Iic k, d' t by
              simpa [off'] using offset_add_eq d' k]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext j
          constructor
          ·
            intro
            exact Finset.mem_univ _
          ·
            intro
            have hj : (j : ℕ) < n := j.isLt
            simp only [Finset.mem_Iic, Fin.le_def, hk]
            omega
        rw [h1, hsum']
      have hex (a : Fin (m - d0)) :
        ∃ k : Fin n, (a : ℕ) ∈ Finset.Ico (off' k) (off' k + d' k) := by
        have hn : 0 < n := by
          by_contra hn0
          have hn0' : n = 0 := by omega
          have hm0 : m - d0 = 0 := by
            simpa [hn0'] using hsum'.symm
          have halt : (a : ℕ) < m - d0 := a.isLt
          omega
        let k0 : Fin n := ⟨0, hn⟩
        have hk0 : off' k0 ≤ (a : ℕ) := by
          have : off' k0 = 0 := by
            simp only [off', k0]
            refine Finset.sum_eq_zero fun i hi =>
              absurd (Fin.lt_def.mp (Finset.mem_Iio.mp hi)) (Nat.not_lt_zero _)
          rw [this]
          exact Nat.zero_le _
        let S := (Finset.univ : Finset (Fin n)).filter fun k => off' k ≤ (a : ℕ)
        have hSne : S.Nonempty := ⟨k0, by simp [S, hk0]⟩
        let k := S.max' hSne
        have hkS : off' k ≤ (a : ℕ) := (Finset.mem_filter.mp (S.max'_mem hSne)).2
        refine ⟨k, Finset.mem_Ico.mpr ⟨hkS, ?_⟩⟩
        by_contra hge
        push Not at hge
        have hge' : off' k + d' k ≤ (a : ℕ) := hge
        if hlast : (k : ℕ) + 1 < n then
          have hks : off' ⟨(k : ℕ) + 1, hlast⟩ ≤ (a : ℕ) := by
            rwa [hoff'_succ k hlast]
          have hmem : ⟨(k : ℕ) + 1, hlast⟩ ∈ S := by
            simp [S, hks]
          have : (k : ℕ) < (⟨(k : ℕ) + 1, hlast⟩ : Fin n) := by
            simp
          exact absurd this (not_lt_of_ge (Finset.le_max' S _ hmem))
        else
          have hk1 : (k : ℕ) = n - 1 := by omega
          have hEq : off' k + d' k = m - d0 := hoff'_last k hk1
          have hle : off' k + d' k ≤ (a : ℕ) := hge
          rw [hEq] at hle
          exact absurd a.isLt (not_lt_of_ge hle)
      have huniq (a : ℕ) (k₁ k₂ : Fin n)
        (h1 : a ∈ Finset.Ico (off' k₁) (off' k₁ + d' k₁))
        (h2 : a ∈ Finset.Ico (off' k₂) (off' k₂ + d' k₂)) : k₁ = k₂ := by
        refine offset_unique d' a ?_ ?_
        · convert h1
        · convert h2
      let σ : (Σ k : Fin n, Fin (d' k)) ≃ Fin (m - d0) := by
        refine Equiv.ofBijective
          (fun p => ⟨off' p.1 + (p.2 : ℕ), by
            have := p.2.isLt
            have h2 := hoff'_le p.1
            omega⟩) ?_
        constructor
        ·
          intro ⟨k₁, i₁⟩ ⟨k₂, i₂⟩ heq
          have heq' : off' k₁ + (i₁ : ℕ) = off' k₂ + (i₂ : ℕ) := by
            simpa using congrArg Fin.val heq
          have ha1 : off' k₁ + (i₁ : ℕ) ∈ Finset.Ico (off' k₁) (off' k₁ + d' k₁) := by
            have := i₁.isLt
            exact Finset.mem_Ico.mpr (by omega)
          have ha2 : off' k₁ + (i₁ : ℕ) ∈ Finset.Ico (off' k₂) (off' k₂ + d' k₂) := by
            rw [heq']
            have := i₂.isLt
            exact Finset.mem_Ico.mpr (by omega)
          have hk : k₁ = k₂ := huniq (off' k₁ + (i₁ : ℕ)) k₁ k₂ ha1 ha2
          subst hk
          congr
          exact Fin.ext (by omega)
        ·
          intro a
          obtain ⟨k, hk⟩ := hex a
          have hka := Finset.mem_Ico.mp hk
          refine ⟨⟨k, ⟨(a : ℕ) - off' k, by omega⟩⟩, ?_⟩
          ext
          simp
          omega
      have hσ (k : Fin n) (i : Fin (d' k)) : (σ ⟨k, i⟩ : ℕ) = off' k + (i : ℕ) := rfl
      set C : ∀ k : Fin n, Matrix (Fin (d' k)) (Fin (d' k)) ℝ := fun k =>
        Matrix.of fun (i j : Fin (d' k)) =>
          ((i : ℕ).choose j : ℝ) *
            ∑ h ∈ Finset.range (d0 + 1),
              (d0.choose h : ℝ) * (-x0) ^ (d0 - h) * (x' k) ^ h *
                (h : ℝ) ^ (i - j : ℤ) with hC
      set As : ∀ k : Fin n, Matrix (Fin (d' k)) (Fin (m - d0)) ℝ := fun k =>
        Matrix.of fun (i : Fin (d' k)) (j : Fin (m - d0)) =>
          ((j : ℝ) + 0) ^ (i : ℕ) * (x' k) ^ (j : ℕ) with hAs
      set Aσ : Matrix (Σ k : Fin n, Fin (d' k)) (Fin m) ℝ :=
        Matrix.of fun (p : Σ k : Fin n, Fin (d' k)) (j : Fin m) =>
          (j : ℝ) ^ (p.2 : ℕ) * (x' p.1) ^ (j : ℕ) with hAσ
      set Asσ : Matrix (Σ k : Fin n, Fin (d' k)) (Fin (m - d0)) ℝ :=
        Matrix.of fun (p : Σ k : Fin n, Fin (d' k)) (j : Fin (m - d0)) =>
          ((j : ℝ) + 0) ^ (p.2 : ℕ) * (x' p.1) ^ (j : ℕ) with hAsσ
      have hA_sub : A_rest.submatrix σ id = Aσ := by
        ext ⟨k, i⟩ j
        simp only [Matrix.submatrix_apply, id, hA_rest, hAσ, Matrix.of_apply, hσ]
        have hmem : off' k + (i : ℕ) ∈ Finset.Ico (off' k) (off' k + d' k) := by
          have := i.isLt
          exact Finset.mem_Ico.mpr (by omega)
        rw [Finset.sum_eq_single k]
        ·
          rw [ite_eq_left hmem, Nat.add_sub_cancel_left (off' k) (i : ℕ), mul_comm,
            add_zero]
        ·
          intro k' _ hk'
          have : ¬(off' k + (i : ℕ) ∈ Finset.Ico (off' k') (off' k' + d' k')) := by
            intro hkmem
            exact hk' (huniq (off' k + (i : ℕ)) k k' hmem hkmem).symm
          simp [this]
        ·
          intro h
          exact absurd (Finset.mem_univ k) h
      have hM_sub : M_rest.submatrix σ id = Asσ := by
        ext ⟨k, i⟩ j
        simp only [Matrix.submatrix_apply, id, hM_rest, hAsσ, Matrix.of_apply, hσ]
        have hmem : off' k + (i : ℕ) ∈ Finset.Ico (off' k) (off' k + d' k) := by
          have := i.isLt
          exact Finset.mem_Ico.mpr (by omega)
        rw [Finset.sum_eq_single k]
        ·
          rw [ite_eq_left hmem, Nat.add_sub_cancel_left (off' k) (i : ℕ)]
          simp [add_zero]
        ·
          intro k' _ hk'
          have : ¬(off' k + (i : ℕ) ∈ Finset.Ico (off' k') (off' k' + d' k')) := by
            intro hkmem
            exact hk' (huniq (off' k + (i : ℕ)) k k' hmem hkmem).symm
          simp [this]
        ·
          intro h
          exact absurd (Finset.mem_univ k) h
      have hAkBd (k : Fin n) :
        (Matrix.of fun (i : Fin (d' k)) (j : Fin m) =>
            (j : ℝ) ^ (i : ℕ) * (x' k) ^ (j : ℕ)) * Bd =
          C k * As k := by
        have hB :
            (Matrix.of fun (i : Fin (d' k)) (j : Fin m) =>
                (j : ℝ) ^ (i : ℕ) * (x' k) ^ (j : ℕ)) =
              Matrix.of fun (i : Fin (d' k)) (j : Fin m) =>
                x' k ^ (j : ℕ) * ((j : ℝ) + 0) ^ (i : ℕ) := by
          ext i j
          simp [Matrix.of_apply, mul_comm, add_zero]
        rw [hB, hC, hAs, hBd]
        simpa using
          (MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf
            (n := d' k) (m := m) (d := d0) (x := x' k) (δ := 0) (l := x0))
      have hAσBd : Aσ * Bd = blockDiagonal' C * Asσ := by
        ext ⟨k, i⟩ j
        have hL :
          (Aσ * Bd) ⟨k, i⟩ j =
            ((Matrix.of fun (i : Fin (d' k)) (j : Fin m) =>
                (j : ℝ) ^ (i : ℕ) * (x' k) ^ (j : ℕ)) * Bd) i j := by
          simp [Matrix.mul_apply, hAσ, Matrix.of_apply]
        have hR :
          (blockDiagonal' C * Asσ) ⟨k, i⟩ j = (C k * As k) i j := by
          simp only [Matrix.mul_apply, hAsσ, Matrix.of_apply]
          rw [Fintype.sum_sigma]
          refine (Finset.sum_eq_single k ?_ ?_).trans ?_
          ·
            intro k' _ hk'
            refine Finset.sum_eq_zero fun i' _ => ?_
            rw [Matrix.blockDiagonal'_apply_ne C i i' hk'.symm]
            simp
          ·
            intro h
            exact absurd (Finset.mem_univ k) h
          ·
            simp_rw [Matrix.blockDiagonal'_apply_eq]
            rfl
        rw [hL, hR, hAkBd]
      have hRest :
        (A_rest * Bd).submatrix σ σ =
          blockDiagonal' C * (M_rest.submatrix σ σ) := by
        have h1 : (A_rest * Bd).submatrix σ σ =
          (A_rest.submatrix σ id * Bd).submatrix id σ := by
          ext x y
          simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply]
        rw [h1]
        have htmp : A_rest.submatrix σ id * Bd = blockDiagonal' C * Asσ := by
          rw [hA_sub, hAσBd]
        rw [htmp]
        have h4 : (blockDiagonal' C * Asσ).submatrix id σ =
          blockDiagonal' C * Asσ.submatrix id σ := by
          ext x y
          simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply]
        have h3 : Asσ.submatrix id σ = M_rest.submatrix σ σ := by
          rw [← hM_sub, Matrix.submatrix_submatrix]
          simp
        rw [h4, h3]
      have hCdet_block : (blockDiagonal' C).det = ∏ k : Fin n, (C k).det := by
        rw [(blockTriangular_blockDiagonal' C).det_fintype]
        refine Fintype.prod_congr _ _ fun k => ?_
        let e : Subtype (fun (p : Σ t : Fin n, Fin (d' t)) => p.1 = k) ≃ Fin (d' k) :=
          Equiv.sigmaSubtype k
        rw [← Matrix.det_reindex_self e]
        congr 1
        ext i j
        have hi : ↑(e.symm i) = (⟨k, i⟩ : Σ t : Fin n, Fin (d' t)) :=
          congrArg Subtype.val (rfl : e.symm i = ⟨⟨k, i⟩, rfl⟩)
        have hj : ↑(e.symm j) = (⟨k, j⟩ : Σ t : Fin n, Fin (d' t)) :=
          congrArg Subtype.val (rfl : e.symm j = ⟨⟨k, j⟩, rfl⟩)
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
          Matrix.of_apply, Matrix.blockDiagonal'_apply_eq, hi, hj]
      have hCk (k : Fin n) : (C k).det = (x' k - x0) ^ (d' k * d0) := by
        rw [hC, mul_comm (d' k) d0]
        exact DetOf.eq.PowSub__Mul (n := d' k) (d := d0) (x := x' k) (l := x0)
      calc
        _ = ((A_rest * Bd).submatrix σ σ).det :=
          (Matrix.det_submatrix_equiv_self (A := A_rest * Bd) (e := σ)).symm
        _ = (blockDiagonal' C * (M_rest.submatrix σ σ)).det := by rw [hRest]
        _ = (blockDiagonal' C).det * (M_rest.submatrix σ σ).det := by rw [Matrix.det_mul]
        _ = (∏ k : Fin n, (C k).det) * M_rest.det := by
          rw [hCdet_block, Matrix.det_submatrix_equiv_self (e := σ)]
        _ = (∏ k : Fin n, (x' k - x0) ^ (d' k * d0)) * M_rest.det := by
          simp only [hCk]
    rw [hRestBd] at hmain
    have hM_rest_det :
      M_rest.det =
        (∏ k : Fin n, (x' k) ^ ((d' k).choose 2)) *
          (∏ k : Fin n, ∏ ℓ : Fin n,
            if (k : ℕ) < (ℓ : ℕ) then (x' ℓ - x' k) ^ (d' ℓ * d' k) else 1) *
          (∏ k : Fin n, ∏ i ∈ Finset.range (d' k), (i ! : ℝ)) := by
      have := ih (x := x') (d := d') hsum'
      convert this
    rw [hM_rest_det] at hmain
    have hLHS :
      M.det =
        (Matrix.of fun (i j : Fin m) =>
            ∑ k : Fin (n + 1),
              if (i : ℕ) ∈ Finset.Ico (∑ t ∈ Finset.Iio k, d t) ((∑ t ∈ Finset.Iio k, d t) + d k) then
                (j : ℝ) ^ ((i : ℕ) - ∑ t ∈ Finset.Iio k, d t) *
                  (x k) ^ (j : ℕ)
              else
                0).det := by
      simp only [hM, off]
    rw [← hLHS, ← hmain]
    rw [pair_prod_succ (x := x) (d := d)]
    simp only [Fin.prod_univ_succ, hx0, hd0, hx', hd']
    ring


-- created on 2026-10-23
-- updated on 2026-10-24
