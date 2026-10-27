import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Interval.Finset.Fin
import Lemma.Finset.AddSumIio.eq.SumIic
import Lemma.Finset.Any_In_IcoSumIio_SumIic.of.Eq_Sum
import Lemma.Finset.Eq.of.In_IcoSumIio_SumIic.In_IcoSumIio_SumIic
import Lemma.Matrix.DetStack_Mul_Sum_Mul_Pow_Sub.eq.PowSub__Mul
import Lemma.Matrix.DetMulStackS_MulPow.eq.Mul_Prod_Factorial.of.Le
import Lemma.Matrix.MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf
import Lemma.Matrix.MulOfPowAddOfPowNegChoose.eq.Zero
import Syntax.LinearAlgebra.Matrix.Notation
import Theorem.Function
open Matrix Finset Nat
set_option maxHeartbeats 999999


private lemma pair_prod_succ
  [Field R]
  {n : ℕ}
  {x : Fin (n + 1) ⇀ R}
  {d : Fin (n + 1) ⇀ ℕ} :
-- imply
  (∏ ℓ : Fin (n + 1), ∏ k ∈ Finset.Iio ℓ, (x[ℓ] - x[k]) ^ (d[ℓ] * d[k])) =
    (∏ k : Fin n, (x[k.succ] - x[0]) ^ (d[k.succ] * d[0])) *
      (∏ ℓ : Fin n, ∏ k ∈ Finset.Iio ℓ,
        (x[ℓ.succ] - x[k.succ]) ^ (d[ℓ.succ] * d[k.succ])) := by
-- proof
  rw [Fin.prod_univ_succ]
  have h0 : (∏ k ∈ Finset.Iio (0 : Fin (n + 1)), (x[0] - x[k]) ^ (d[0] * d[k])) = 1 := by
    refine Eq.trans (Finset.prod_congr ?_ fun _ _ => rfl) Finset.prod_empty
    ext k
    simp [Finset.mem_Iio]
  have hsucc (ℓ : Fin n) :
    (∏ k ∈ Finset.Iio ℓ.succ, (x[ℓ.succ] - x[k]) ^ (d[ℓ.succ] * d[k])) =
      (x[ℓ.succ] - x[0]) ^ (d[ℓ.succ] * d[0]) *
        ∏ k ∈ Finset.Iio ℓ, (x[ℓ.succ] - x[k.succ]) ^ (d[ℓ.succ] * d[k.succ]) := by
    have hset :
      Finset.Iio ℓ.succ =
        insert (0 : Fin (n + 1)) ((Finset.Iio ℓ).map (Fin.succEmb n)) := by
      rw [Fin.map_succEmb_Iio ℓ, Finset.Ioo_insert_left (Fin.succ_pos ℓ)]
      ext i
      simp [Finset.mem_Ico, Finset.mem_Iio]
    have hnotin : (0 : Fin (n + 1)) ∉ (Finset.Iio ℓ).map (Fin.succEmb n) := by
      simp
    rw [hset, Finset.prod_insert hnotin, Finset.prod_map]
    rfl
  simp only [h0, one_mul]
  simp_rw [hsucc]
  rw [Finset.prod_mul_distrib]

/-- n-base geometric Vandermonde by induction on `n`. -/
@[path]
private lemma main
  [Field R] [CharZero R]
  {n m : ℕ}
  {x : Fin n ⇀ R}
  {d : Fin n ⇀ ℕ}
-- given
  (h : ∑ k, d[k] = m) :
-- imply
  ([i < m, j < m]
    ∑ k : Fin n,
      if (i : ℕ) ∈ Finset.Ico (∑ t ∈ Finset.Iio k, d[t])
          (∑ t ∈ Finset.Iic k, d[t]) then
        (j : R) ^ ((i : ℕ) - ∑ t ∈ Finset.Iio k, d[t]) * x[k] ^ (j : ℕ)
      else
        0).det =
    ∏ i : Fin n,
      (∏ j ∈ Finset.Iio i, (x[i] - x[j]) ^ (d[i] * d[j])) *
        (∏ j ∈ Finset.range d[i], (j ! : R)) *
        x[i] ^ (d[i].choose 2) := by
-- proof
  have hprod :
    (∏ i : Fin n,
      (∏ j ∈ Finset.Iio i, (x[i] - x[j]) ^ (d[i] * d[j])) *
        (∏ j ∈ Finset.range d[i], (j ! : R)) *
        x[i] ^ (d[i].choose 2)) =
      (∏ i : Fin n, ∏ j ∈ Finset.Iio i, (x[i] - x[j]) ^ (d[i] * d[j])) *
        (∏ i : Fin n, ∏ j ∈ Finset.range d[i], (j ! : R)) *
        (∏ i : Fin n, x[i] ^ (d[i].choose 2)) := by
    simp [mul_assoc, Finset.prod_mul_distrib]
  rw [hprod]
  clear hprod
  induction n generalizing m with
  | zero =>
    have hm0 : m = 0 := by
      simpa [eq_comm] using h
    subst hm0
    simp [Matrix.det_fin_zero]
  | succ n ih =>
    set d0 := d[0] with hd0
    set x0 := x[0] with hx0
    set d' : Fin n ⇀ ℕ := ⟨fun k => d[k.succ]⟩ with hd'
    set x' : Fin n ⇀ R := ⟨fun k => x[k.succ]⟩ with hx'
    have hsum_succ : d0 + ∑ k : Fin n, d'[k] = m := by
      simpa [Fin.sum_univ_succ, d0, d'] using h
    have hsum' : ∑ k : Fin n, d'[k] = m - d0 := by omega
    have hd0le : d0 ≤ m := by omega
    set off : Fin (n + 1) → ℕ := fun k =>
      ∑ t ∈ Finset.Iio k, d[t] with hoff
    set off' : Fin n → ℕ := fun k =>
      ∑ t ∈ Finset.Iio k, d'[t] with hoff'
    have hoff0 : off 0 = 0 := by
      simp [off]
    have hoff_succ (k : Fin n) : off k.succ = d0 + off' k := by
      simp only [off, off', d', d0]
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
    set M := [i < m, j < m]
      ∑ k : Fin (n + 1),
        if (i : ℕ) ∈ Finset.Ico (off k) (off k + d[k]) then
          (j : R) ^ ((i : ℕ) - off k) * x[k] ^ (j : ℕ)
        else
          0 with hM
    set M_rest := [i < (m - d0), j < (m - d0)]
      ∑ k : Fin n,
        if (i : ℕ) ∈ Finset.Ico (off' k) (off' k + d'[k]) then
          (j : R) ^ ((i : ℕ) - off' k) * x'[k] ^ (j : ℕ)
        else
          0 with hM_rest
    set ε₁ : Fin d0 ⊕ Fin (m - d0) ≃ Fin m :=
      finSumFinEquiv.trans (finCongr (by omega : d0 + (m - d0) = m)) with hε₁
    set A₁ := Matrix.of fun (i : Fin d0) (j : Fin m) =>
      x0 ^ (j : ℕ) * ((j : R) + 0) ^ (i : ℕ) with hA₁
    set A_rest := Matrix.of fun (i : Fin (m - d0)) (j : Fin m) =>
      ∑ k : Fin n,
        if (i : ℕ) ∈ Finset.Ico (off' k) (off' k + d'[k]) then
          x'[k] ^ (j : ℕ) * ((j : R) + 0) ^ ((i : ℕ) - off' k)
        else
          0 with hA_rest
    set B₁ := Matrix.of fun (k : Fin m) (j : Fin d0) =>
      (-x0) ^ ((j : ℤ) - (k : ℕ)) * ((j : ℕ).choose k : R) with hB₁
    set Bd := Matrix.of fun (i : Fin m) (j : Fin (m - d0)) =>
      (-x0) ^ ((d0 : ℤ) + (j : ℕ) - (i : ℕ)) *
        (if (j : ℕ) ≤ i then (d0.choose ((i : ℕ) - j) : R) else 0) with hBd
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
            if (a : ℕ) ∈ Finset.Ico (off k) (off k + d[k]) then
              (j : R) ^ ((a : ℕ) - off k) * x[k] ^ (j : ℕ)
            else
              0) =
            (j : R) ^ (a : ℕ) * x0 ^ (j : ℕ) := by
          rw [Fin.sum_univ_succ]
          have h0 : (a : ℕ) ∈ Finset.Ico (off 0) (off 0 + d[0]) := by
            simp [hoff0, d0]
          rw [ite_eq_left h0, hoff0, tsub_zero, hx0]
          have hrest :
            (∑ k : Fin n,
              if (a : ℕ) ∈ Finset.Ico (off k.succ) (off k.succ + d[k.succ]) then
                (j : R) ^ ((a : ℕ) - off k.succ) * x[k.succ] ^ (j : ℕ)
              else
                0) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            have : ¬((a : ℕ) ∈ Finset.Ico (off k.succ) (off k.succ + d[k.succ])) := by
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
        have h0 : ¬(d0 + (a : ℕ) ∈ Finset.Ico (off 0) (off 0 + d[0])) := by
          simp [hoff0, d0]
        rw [ite_eq_right h0, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hoff_succ k]
        simp only [d', x']
        if hk : (a : ℕ) ∈ Finset.Ico (off' k) (off' k + d'[k]) then
          have hk' :
            d0 + (a : ℕ) ∈ Finset.Ico (d0 + off' k) (d0 + off' k + d'[k]) := by
            have h := Finset.mem_Ico.mp hk
            exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          rw [ite_eq_left hk', ite_eq_left hk, mul_comm, add_zero]
          congr 2
          omega
        else
          have hk' :
            ¬(d0 + (a : ℕ) ∈ Finset.Ico (d0 + off' k) (d0 + off' k + d'[k])) := by
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
        MulOfPowAddOfPowNegChoose.eq.Zero (δ := (0 : R)) (x := x0) (d := d0) (m := m)
    rw [hz, Matrix.det_fromBlocks_zero₁₂, hA₁, hB₁,
      DetMulStackS_MulPow.eq.Mul_Prod_Factorial.of.Le hd0le] at hmain
    have hRestBd :
      (A_rest * Bd).det =
        (∏ k : Fin n, (x'[k] - x0) ^ (d'[k] * d0)) * M_rest.det := by
      have hoff'_le (k : Fin n) : off' k + d'[k] ≤ m - d0 := by
        have h1 : off' k + d'[k] = ∑ t ∈ Finset.Iic k, d'[t] := by
          simpa [off'] using AddSumIio.eq.SumIic d' k
        rw [h1, ← hsum']
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hex (a : Fin (m - d0)) :
        ∃ k : Fin n, (a : ℕ) ∈ Finset.Ico (off' k) (off' k + d'[k]) := by
        obtain ⟨k, hk⟩ := Any_In_IcoSumIio_SumIic.of.Eq_Sum hsum' a
        refine ⟨k, ?_⟩
        have h := AddSumIio.eq.SumIic d' k
        dsimp only [GetElem.getElem] at hk h
        rw [Finset.mem_Ico] at hk ⊢
        simp only [off']
        rw [h]
        apply hk
      have huniq (a : ℕ) (k₁ k₂ : Fin n)
        (h1 : a ∈ Finset.Ico (off' k₁) (off' k₁ + d'[k₁]))
        (h2 : a ∈ Finset.Ico (off' k₂) (off' k₂ + d'[k₂])) : k₁ = k₂ := by
        refine Eq.of.In_IcoSumIio_SumIic.In_IcoSumIio_SumIic (d := d') (t := a) ?_ ?_
        ·
          have h := AddSumIio.eq.SumIic d' k₁
          simp only [off'] at h1
          rw [Finset.mem_Ico] at h1 ⊢
          rw [← h]
          apply h1
        ·
          have h := AddSumIio.eq.SumIic d' k₂
          simp only [off'] at h2
          rw [Finset.mem_Ico] at h2 ⊢
          rw [← h]
          apply h2
      let σ : (Σ k : Fin n, Fin d'[k]) ≃ Fin (m - d0) := by
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
          have ha1 : off' k₁ + (i₁ : ℕ) ∈ Finset.Ico (off' k₁) (off' k₁ + d'[k₁]) := by
            have := i₁.isLt
            exact Finset.mem_Ico.mpr (by omega)
          have ha2 : off' k₁ + (i₁ : ℕ) ∈ Finset.Ico (off' k₂) (off' k₂ + d'[k₂]) := by
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
      have hσ (k : Fin n) (i : Fin d'[k]) : (σ ⟨k, i⟩ : ℕ) = off' k + (i : ℕ) := rfl
      set C : ∀ k : Fin n, Matrix (Fin d'[k]) (Fin d'[k]) R := fun k =>
        [i < d'[k], j < d'[k]]
          ((i : ℕ).choose j : R) *
            ∑ h ∈ Finset.range (d0 + 1),
              (d0.choose h : R) * (-x0) ^ (d0 - h) * x'[k] ^ h *
                (h : R) ^ (i - j : ℤ) with hC
      set As : ∀ k : Fin n, Matrix (Fin d'[k]) (Fin (m - d0)) R := fun k =>
        Matrix.of fun (i : Fin d'[k]) (j : Fin (m - d0)) =>
          ((j : R) + 0) ^ (i : ℕ) * x'[k] ^ (j : ℕ) with hAs
      set Aσ : Matrix (Σ k : Fin n, Fin d'[k]) (Fin m) R :=
        Matrix.of fun (p : Σ k : Fin n, Fin d'[k]) (j : Fin m) =>
          (j : R) ^ (p.2 : ℕ) * x'[p.1] ^ (j : ℕ) with hAσ
      set Asσ : Matrix (Σ k : Fin n, Fin d'[k]) (Fin (m - d0)) R :=
        Matrix.of fun (p : Σ k : Fin n, Fin d'[k]) (j : Fin (m - d0)) =>
          ((j : R) + 0) ^ (p.2 : ℕ) * x'[p.1] ^ (j : ℕ) with hAsσ
      have hA_sub : A_rest.submatrix σ id = Aσ := by
        ext ⟨k, i⟩ j
        simp only [Matrix.submatrix_apply, id, hA_rest, hAσ, Matrix.of_apply, hσ]
        have hmem : off' k + (i : ℕ) ∈ Finset.Ico (off' k) (off' k + d'[k]) := by
          have := i.isLt
          exact Finset.mem_Ico.mpr (by omega)
        rw [Finset.sum_eq_single k]
        ·
          rw [ite_eq_left hmem, Nat.add_sub_cancel_left (off' k) (i : ℕ), mul_comm,
            add_zero]
        ·
          intro k' _ hk'
          have : ¬(off' k + (i : ℕ) ∈ Finset.Ico (off' k') (off' k' + d'[k'])) := by
            intro hkmem
            exact hk' (huniq (off' k + (i : ℕ)) k k' hmem hkmem).symm
          simp [this]
        ·
          intro h
          exact absurd (Finset.mem_univ k) h
      have hM_sub : M_rest.submatrix σ id = Asσ := by
        ext ⟨k, i⟩ j
        simp only [Matrix.submatrix_apply, id, hM_rest, hAsσ, Matrix.ofFun_apply, hσ]
        have hmem : off' k + (i : ℕ) ∈ Finset.Ico (off' k) (off' k + d'[k]) := by
          have := i.isLt
          exact Finset.mem_Ico.mpr (by omega)
        rw [Finset.sum_eq_single k]
        ·
          rw [ite_eq_left hmem, Nat.add_sub_cancel_left (off' k) (i : ℕ)]
          simp [add_zero]
        ·
          intro k' _ hk'
          have : ¬(off' k + (i : ℕ) ∈ Finset.Ico (off' k') (off' k' + d'[k'])) := by
            intro hkmem
            exact hk' (huniq (off' k + (i : ℕ)) k k' hmem hkmem).symm
          simp [this]
        ·
          intro h
          exact absurd (Finset.mem_univ k) h
      have hAkBd (k : Fin n) :
        (Matrix.of fun (i : Fin d'[k]) (j : Fin m) =>
          (j : R) ^ (i : ℕ) * x'[k] ^ (j : ℕ)) * Bd =
          C k * As k := by
        have hB :
          (Matrix.of fun (i : Fin d'[k]) (j : Fin m) =>
            (j : R) ^ (i : ℕ) * x'[k] ^ (j : ℕ)) =
            Matrix.of fun (i : Fin d'[k]) (j : Fin m) =>
              x'[k] ^ (j : ℕ) * ((j : R) + 0) ^ (i : ℕ) := by
          ext i j
          simp [Matrix.of_apply, mul_comm, add_zero]
        rw [hB, hC, hAs, hBd]
        simpa [Matrix.ofFun] using
          (MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf
            (n := d'[k]) (m := m) (d := d0) (x := x'[k]) (δ := 0) (l := x0))
      have hAσBd : Aσ * Bd = blockDiagonal' C * Asσ := by
        ext ⟨k, i⟩ j
        have hL :
          (Aσ * Bd) ⟨k, i⟩ j =
            ((Matrix.of fun (i : Fin d'[k]) (j : Fin m) =>
              (j : R) ^ (i : ℕ) * x'[k] ^ (j : ℕ)) * Bd) i j := by
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
        let e : Subtype (fun (p : Σ t : Fin n, Fin d'[t]) => p.1 = k) ≃ Fin d'[k] :=
          Equiv.sigmaSubtype k
        rw [← Matrix.det_reindex_self e]
        congr 1
        ext i j
        have hi : ↑(e.symm i) = (⟨k, i⟩ : Σ t : Fin n, Fin d'[t]) :=
          congrArg Subtype.val (rfl : e.symm i = ⟨⟨k, i⟩, rfl⟩)
        have hj : ↑(e.symm j) = (⟨k, j⟩ : Σ t : Fin n, Fin d'[t]) :=
          congrArg Subtype.val (rfl : e.symm j = ⟨⟨k, j⟩, rfl⟩)
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
          Matrix.of_apply, Matrix.blockDiagonal'_apply_eq, hi, hj]
      have hCk (k : Fin n) : (C k).det = (x'[k] - x0) ^ (d'[k] * d0) := by
        rw [hC]
        exact DetStack_Mul_Sum_Mul_Pow_Sub.eq.PowSub__Mul (n := d'[k]) (d := d0) (x := x'[k]) (l := x0)
      calc
        _ = ((A_rest * Bd).submatrix σ σ).det :=
          (Matrix.det_submatrix_equiv_self (A := A_rest * Bd) (e := σ)).symm
        _ = (blockDiagonal' C * (M_rest.submatrix σ σ)).det := by rw [hRest]
        _ = (blockDiagonal' C).det * (M_rest.submatrix σ σ).det := by rw [Matrix.det_mul]
        _ = (∏ k : Fin n, (C k).det) * M_rest.det := by
          rw [hCdet_block, Matrix.det_submatrix_equiv_self (e := σ)]
        _ = (∏ k : Fin n, (x'[k] - x0) ^ (d'[k] * d0)) * M_rest.det := by
          simp only [hCk]
    rw [hRestBd] at hmain
    have hM_rest_det :
      M_rest.det =
        (∏ ℓ : Fin n, ∏ k ∈ Finset.Iio ℓ,
            (x'[ℓ] - x'[k]) ^ (d'[ℓ] * d'[k])) *
          (∏ k : Fin n, ∏ i ∈ Finset.range d'[k], (i ! : R)) *
          (∏ k : Fin n, x'[k] ^ (d'[k].choose 2)) := by
      have hih := ih (x := x') (d := d') hsum'
      have hshape :
        M_rest =
          ([i < (m - d0), j < (m - d0)]
            ∑ k : Fin n,
              if (i : ℕ) ∈ Finset.Ico (∑ t ∈ Finset.Iio k, d'[t])
                  (∑ t ∈ Finset.Iic k, d'[t]) then
                (j : R) ^ ((i : ℕ) - ∑ t ∈ Finset.Iio k, d'[t]) *
                  x'[k] ^ (j : ℕ)
              else
                0) := by
        ext i j
        simp only [hM_rest, off', Matrix.ofFun_apply]
        refine Fintype.sum_congr _ _ fun k => ?_
        simp_rw [AddSumIio.eq.SumIic]
      rwa [hshape]
    rw [hM_rest_det] at hmain
    have hLHS :
      M.det =
        ([i < m, j < m]
          ∑ k : Fin (n + 1),
            if (i : ℕ) ∈ Finset.Ico (∑ t ∈ Finset.Iio k, d[t])
                (∑ t ∈ Finset.Iic k, d[t]) then
              (j : R) ^ ((i : ℕ) - ∑ t ∈ Finset.Iio k, d[t]) *
                x[k] ^ (j : ℕ)
            else
              0).det := by
      simp only [hM, off]
      congr 1
      ext i j
      simp only [Matrix.ofFun_apply]
      refine Fintype.sum_congr _ _ fun k => ?_
      simp_rw [AddSumIio.eq.SumIic]
    rw [← hLHS, ← hmain]
    rw [pair_prod_succ (x := x) (d := d)]
    simp only [Fin.prod_univ_succ, hx0, hd0, hx', hd']
    ring


-- created on 2026-10-23
-- updated on 2026-10-27
