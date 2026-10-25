import Lemma.Finset.AddSumIio.eq.SumIic
import Lemma.Finset.Any_In_Ico_SumIioSumIic.of.Eq_Sum
import Lemma.Finset.Eq.of.In_Ico_SumIioSumIic.In_Ico_SumIioSumIic
import Lemma.Matrix.DetStack_Sum_Ite.eq.Prod_MulMulProdS.of.EqSum
import Lemma.Polynomial.Any_Eq_Prod_SubXC.of.EqNatDegree.Monic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Function
import sympy.vector.FinDot
open Polynomial Matrix Finset
set_option maxHeartbeats 999999


private lemma rootMultiplicity_prod_linear
  (n : ℕ)
  (r : Fin n → ℂ)
  (z : ℂ) :
  (∏ i : Fin n, (X - C (r i))).rootMultiplicity z =
    Finset.card {i : Fin n | r i = z} := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have hne :
      (X - C (r 0)) * ∏ i : Fin n, (X - C (r i.succ)) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _)
    rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C, ih (fun i => r i.succ)]
    classical
    have hcard :
      Finset.card {i : Fin (n + 1) | r i = z} =
          (if r 0 = z then 1 else 0) +
            Finset.card {i : Fin n | r i.succ = z} := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ, ← Finset.sum_filter,
        ← Finset.card_eq_sum_ones]
    rw [hcard]
    if h0 : r 0 = z then
      rw [ite_eq_left h0, ite_eq_left h0.symm]
    else
      rw [ite_eq_right h0, ite_eq_right (Ne.symm h0)]

private lemma falling_det_mul_Q
  {r n : ℕ}
  (x : Fin r → ℂ)
  (d : Fin r → ℕ)
  (hsum : ∑ k : Fin r, d k = n) :
  (Matrix.of fun (t i : Fin n) =>
    ∑ k : Fin r,
      if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
        (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
          x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
      else 0).det *
    (∏ k : Fin r, x k ^ (d k).choose 2) =
  (∏ k : Fin r, ∏ j ∈ Finset.Iio k, (x k - x j) ^ (d k * d j)) *
    (∏ k : Fin r, ∏ j ∈ Finset.range (d k), ((Nat.factorial j) : ℂ)) *
    (∏ k : Fin r, x k ^ (d k).choose 2) := by
  classical
  let Q : ℂ := ∏ k : Fin r, x k ^ (d k).choose 2
  let Vand : ℂ := ∏ k : Fin r, ∏ j ∈ Finset.Iio k, (x k - x j) ^ (d k * d j)
  let Fact : ℂ := ∏ k : Fin r, ∏ j ∈ Finset.range (d k), (Nat.factorial j)
  let off (k : Fin r) : ℕ := ∑ j ∈ Finset.Iio k, d j
  let slot (p : Σ k : Fin r, Fin (d k)) : Fin n :=
    ⟨off p.1 + p.2.val, by
      have hlt : p.2.val < d p.1 := p.2.isLt
      have hle : off p.1 + d p.1 ≤ n := by
        rw [show off p.1 + d p.1 = ∑ j ∈ Finset.Iic p.1, d j by
          have h := AddSumIio.eq.SumIic (Fun.mk d) p.1
          dsimp only [GetElem.getElem] at h
          simpa [off] using h]
        rw [← hsum]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega⟩
  have slot_inj : Function.Injective slot := by
    intro p q hpq
    obtain ⟨k₁, a₁⟩ := p
    obtain ⟨k₂, a₂⟩ := q
    have hval : off k₁ + a₁.val = off k₂ + a₂.val := by
      have := congrArg Fin.val hpq
      simpa [slot] using this
    let i : Fin n := slot ⟨k₁, a₁⟩
    have hi₁ :
      (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k₁, d j) (∑ j ∈ Finset.Iic k₁, d j) := by
      simp only [Finset.mem_Ico, i, slot]
      constructor
      · exact Nat.le_add_right _ _
      ·
        have h := AddSumIio.eq.SumIic (Fun.mk d) k₁
        dsimp only [GetElem.getElem] at h
        rw [← h]
        exact Nat.add_lt_add_left a₁.isLt _
    have hi₂ :
      (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k₂, d j) (∑ j ∈ Finset.Iic k₂, d j) := by
      simp only [Finset.mem_Ico]
      constructor
      ·
        have : off k₂ ≤ i := by
          simp only [i, slot]
          rw [hval]
          exact Nat.le_add_right _ _
        simpa [off] using this
      ·
        have h := AddSumIio.eq.SumIic (Fun.mk d) k₂
        dsimp only [GetElem.getElem] at h
        rw [← h]
        have : i = off k₂ + a₂.val := by
          simpa [i, slot] using hval
        rw [this]
        exact Nat.add_lt_add_left a₂.isLt _
    have hk : k₁ = k₂ := by
      refine Eq.of.In_Ico_SumIioSumIic.In_Ico_SumIioSumIic
        (d := Fun.mk d) (t := i) (k₁ := k₁) (k₂ := k₂) ?_ ?_
      ·
        dsimp only [GetElem.getElem]
        apply hi₁
      ·
        dsimp only [GetElem.getElem]
        apply hi₂
    subst hk
    have ha : a₁.val = a₂.val := by
      simpa [off] using hval
    have : a₁ = a₂ := Fin.ext ha
    subst this
    rfl
  have slot_surj : Function.Surjective slot := by
    intro i
    obtain ⟨k, hk⟩ := show
      ∃ k : Fin r, (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) by
        have hsumd : ∑ k : Fin r, (Fun.mk d)[k] = n := by
          simpa [Fun.getElem_eq] using hsum
        obtain ⟨k, hk⟩ := Any_In_Ico_SumIioSumIic.of.Eq_Sum hsumd i
        refine ⟨k, ?_⟩
        dsimp only [GetElem.getElem] at hk
        apply hk
    simp only [Finset.mem_Ico] at hk
    have hle : off k ≤ i := by
      simpa [off] using hk.1
    have hupper : i < off k + d k := by
      have heq : off k + d k = ∑ j ∈ Finset.Iic k, d j := by
        have h := AddSumIio.eq.SumIic (Fun.mk d) k
        dsimp only [GetElem.getElem] at h
        simpa [off] using h
      simpa [heq] using hk.2
    have hlt : i - off k < d k := (Nat.sub_lt_iff_lt_add' hle).mpr hupper
    refine ⟨⟨k, ⟨i - off k, hlt⟩⟩, ?_⟩
    apply Fin.ext
    simp only [slot]
    exact Nat.add_sub_of_le hle
  let ξ : (Σ k : Fin r, Fin (d k)) ≃ Fin n :=
    Equiv.ofBijective slot ⟨slot_inj, slot_surj⟩
  let block (i : Fin n) : Fin r := (ξ.symm i).1
  let ex (i : Fin n) : ℕ := (ξ.symm i).2.val
  have block_ξ (p : Σ k : Fin r, Fin (d k)) : block (ξ p) = p.1 := by
    simp [block, Equiv.symm_apply_apply]
  have ex_ξ (p : Σ k : Fin r, Fin (d k)) : ex (ξ p) = p.2.val := by
    unfold ex
    rw [Equiv.symm_apply_apply]
  have off_ex (i : Fin n) : off (block i) + ex i = i := by
    have hslot : slot (ξ.symm i) = i := by
      rw [← Equiv.ofBijective_apply slot ⟨slot_inj, slot_surj⟩]
      exact ξ.apply_symm_apply i
    have := congrArg Fin.val hslot
    simpa [slot, block, ex] using this
  have ex_lt (i : Fin n) : ex i < d (block i) := (ξ.symm i).2.isLt
  have hmem (i : Fin n) :
    (i : ℕ) ∈ Finset.Ico (off (block i)) (∑ j ∈ Finset.Iic (block i), d j) := by
    simp only [Finset.mem_Ico]
    constructor
    · exact (Nat.le_add_right (off (block i)) (ex i)).trans_eq (off_ex i)
    ·
      have hex := off_ex i
      have hlt := ex_lt i
      have h := AddSumIio.eq.SumIic (Fun.mk d) (block i)
      dsimp only [GetElem.getElem] at h
      rw [← hex, ← h]
      exact Nat.add_lt_add_left hlt _
  let Φ : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun t i =>
      (t : ℕ).descFactorial (ex i) * x (block i) ^ ((t : ℕ) - ex i)
  let Ψ : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun t i => ((t : ℕ) : ℂ) ^ ex i * x (block i) ^ (t : ℕ)
  let T : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun s i =>
      if block s = block i ∧ ex s ≤ ex i then
        Nat.stirlingSecond (ex i) (ex s) * x (block i) ^ ex s
      else 0
  have hΦ : Φ =
      Matrix.of fun (t i : Fin n) =>
        ∑ k : Fin r,
          if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
            (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
              x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
          else 0 := by
    ext t i
    simp only [Φ, Matrix.of_apply]
    rw [Finset.sum_eq_single_of_mem (block i) (Finset.mem_univ _)]
    ·
      have hi := hmem i
      simp only [off] at hi
      rw [ite_eq_left hi]
      have hex : ex i = i - off (block i) := by
        have h := off_ex i
        rw [← h]
        exact (Nat.add_sub_cancel_left (off (block i)) (ex i)).symm
      simp [hex, off, block]
    ·
      intro k' _ hk'
      have hnot :
        (i : ℕ) ∉ Finset.Ico (∑ j ∈ Finset.Iio k', d j) (∑ j ∈ Finset.Iic k', d j) := by
        intro hkmem
        apply hk'
        refine Eq.of.In_Ico_SumIioSumIic.In_Ico_SumIioSumIic
          (d := Fun.mk d) (t := i) (k₁ := k') (k₂ := block i) ?_ ?_
        ·
          dsimp only [GetElem.getElem]
          apply hkmem
        ·
          have hi := hmem i
          simp only [off] at hi
          dsimp only [GetElem.getElem]
          apply hi
      simp [hnot]
  have htri : T.IsUpperTriangular := by
    intro row col hlt
    simp only [T, Matrix.of_apply]
    split_ifs with hcond
    ·
      exfalso
      have hvals : (col : ℕ) < row := Fin.lt_def.mp hlt
      have hcol := off_ex col
      have hrow := off_ex row
      have hsame : block col = block row := hcond.1.symm
      rw [hsame] at hcol
      omega
    · rfl
  have hdiag (i : Fin n) : T i i = x (block i) ^ ex i := by
    simp [T, Nat.stirlingSecond_self]
  have hTdet : T.det = Q := by
    rw [Matrix.det_of_isUpperTriangular htri]
    simp_rw [hdiag]
    rw [← Fintype.prod_equiv ξ (fun p => x p.1 ^ p.2.val) (fun i => x (block i) ^ ex i)
      (fun p => by simp [block_ξ, ex_ξ])]
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Fin.prod_univ_eq_prod_range (fun a => x k ^ a) (d k)]
    rw [Finset.prod_pow_eq_pow_sum]
    rw [Finset.sum_range_id, ← Nat.choose_two_right]
  have hmul : Ψ = Φ * T := by
    ext t i
    simp only [Matrix.mul_apply]
    let k := block i
    let ei := ex i
    have hrew :=
      Fintype.sum_equiv ξ (fun p => Φ t (ξ p) * T (ξ p) i) (fun s => Φ t s * T s i) fun _ => rfl
    rw [← hrew, Fintype.sum_sigma]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
    ·
      have hinner :
        ∑ a : Fin (d k), Φ t (ξ ⟨k, a⟩) * T (ξ ⟨k, a⟩) i =
            x k ^ (t : ℕ) * ((t : ℕ) : ℂ) ^ ei := by
        have hterm (a : Fin (d k)) :
          Φ t (ξ ⟨k, a⟩) * T (ξ ⟨k, a⟩) i =
              if a.val ≤ ei then
                Nat.stirlingSecond ei a.val * (t : ℕ).descFactorial a.val *
                  x k ^ (t : ℕ)
              else 0 := by
          if ha : a.val ≤ ei then
            rw [ite_eq_left ha]
            have hpos : block (ξ ⟨k, a⟩) = block i ∧ ex (ξ ⟨k, a⟩) ≤ ex i := by
              constructor
              · simp [block_ξ, k]
              · simpa [ex_ξ, ei] using ha
            simp only [Φ, T, Matrix.of_apply]
            rw [ite_eq_left hpos]
            simp only [block_ξ, ex_ξ, k, ei]
            if ht : a.val ≤ (t : ℕ) then
              calc
                _ = Nat.stirlingSecond ei a.val * (t : ℕ).descFactorial a.val *
                    (x k ^ ((t : ℕ) - a.val) * x k ^ a.val) := by ring
                _ = Nat.stirlingSecond ei a.val * (t : ℕ).descFactorial a.val *
                    x k ^ (((t : ℕ) - a.val) + a.val) := by rw [← pow_add]
                _ = Nat.stirlingSecond ei a.val * (t : ℕ).descFactorial a.val *
                    x k ^ (t : ℕ) := by rw [Nat.sub_add_cancel ht]
            else
              simp [(Nat.descFactorial_eq_zero_iff_lt).mpr (Nat.lt_of_not_ge ht)]
          else
            rw [ite_eq_right ha]
            have hneg : ¬ (block (ξ ⟨k, a⟩) = block i ∧ ex (ξ ⟨k, a⟩) ≤ ex i) := by
              intro hcond
              exact ha (by simpa [ex_ξ, ei] using hcond.2)
            simp only [Φ, T, Matrix.of_apply]
            rw [ite_eq_right hneg]
            simp
        simp_rw [hterm]
        have hle : ei + 1 ≤ d k := by
          have := ex_lt i
          simpa [ei, k] using Nat.succ_le_of_lt this
        have hrange :
          ∑ a : Fin (d k),
                (if a.val ≤ ei then
                  Nat.stirlingSecond ei a.val * (t : ℕ).descFactorial a.val *
                    x k ^ (t : ℕ)
                else 0) =
              ∑ j ∈ Finset.range (ei + 1),
                Nat.stirlingSecond ei j * (t : ℕ).descFactorial j *
                  x k ^ (t : ℕ) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_bij'
            (fun a ha => a.val)
            (fun j hj => (⟨j, by
              have hj' : j < ei + 1 := Finset.mem_range.mp hj
              omega⟩ : Fin (d k)))
            ?_ ?_ ?_ ?_ ?_
          ·
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
          ·
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          ·
            intro a ha
            apply Fin.ext
            rfl
          ·
            intro j hj
            rfl
          ·
            intro a ha
            rfl
        rw [hrange]
        have hst : ((t : ℕ) : ℂ) ^ ei =
            ∑ j ∈ Finset.range (ei + 1),
              Nat.stirlingSecond ei j * (t : ℕ).descFactorial j := by
          simpa [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using
            congrArg (Nat.cast : ℕ → ℂ)
              (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial (t : ℕ) ei)
        have hpull :
          ∑ j ∈ Finset.range (ei + 1),
                Nat.stirlingSecond ei j * (t : ℕ).descFactorial j * x k ^ (t : ℕ) =
              x k ^ (t : ℕ) *
                ∑ j ∈ Finset.range (ei + 1),
                  Nat.stirlingSecond ei j * (t : ℕ).descFactorial j := by
          simp_rw [← Nat.cast_mul]
          rw [← Finset.sum_mul, ← Nat.cast_sum, mul_comm]
        rw [hpull, hst]
      rw [hinner]
      simp [Ψ, Matrix.of_apply, k, ei, mul_comm]
    ·
      intro k' _ hk'
      apply Finset.sum_eq_zero
      intro a _
      have hT0 : T (ξ ⟨k', a⟩) i = 0 := by
        simp [T, Matrix.of_apply, block_ξ, ex_ξ, hk', k]
      simp [hT0]
  have hΨdet : Ψ.det = Φ.det * T.det := by
    rw [hmul, Matrix.det_mul]
  let Mmono : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun i j =>
      ∑ k : Fin r,
        if (i : ℕ) ∈ Finset.Ico (∑ t ∈ Finset.Iio k, d t) (∑ t ∈ Finset.Iic k, d t) then
          (j : ℂ) ^ (i - ∑ t ∈ Finset.Iio k, d t) * x k ^ (j : ℕ)
        else 0
  have htrans : Mmono = Ψ.transpose := by
    ext i j
    simp only [Mmono, Ψ, Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single_of_mem (block i) (Finset.mem_univ _)]
    ·
      have hi := hmem i
      simp only [off] at hi
      rw [ite_eq_left hi]
      have hex : ex i = i - off (block i) := by
        have h := off_ex i
        rw [← h]
        exact (Nat.add_sub_cancel_left (off (block i)) (ex i)).symm
      rw [hex]
    ·
      intro k' _ hk'
      have hnot :
        (i : ℕ) ∉ Finset.Ico (∑ t ∈ Finset.Iio k', d t) (∑ t ∈ Finset.Iic k', d t) := by
        intro hkmem
        apply hk'
        refine Eq.of.In_Ico_SumIioSumIic.In_Ico_SumIioSumIic
          (d := Fun.mk d) (t := i) (k₁ := k') (k₂ := block i) ?_ ?_
        ·
          dsimp only [GetElem.getElem]
          apply hkmem
        ·
          have hi := hmem i
          simp only [off] at hi
          dsimp only [GetElem.getElem]
          apply hi
      simp [hnot]
  have hsumF : ∑ k : Fin r, (⟨d⟩ : Fin r ⇀ ℕ)[k] = n := by
    simpa [Fun.getElem_eq] using hsum
  have hlem :=
    DetStack_Sum_Ite.eq.Prod_MulMulProdS.of.EqSum (x := ⟨x⟩) (d := ⟨d⟩) hsumF
  have hsplit :
    (∏ i : Fin r,
        (∏ j ∈ Finset.Iio i, ((⟨x⟩ : Fin r ⇀ ℂ)[i] - (⟨x⟩ : Fin r ⇀ ℂ)[j]) ^
          ((⟨d⟩ : Fin r ⇀ ℕ)[i] * (⟨d⟩ : Fin r ⇀ ℕ)[j])) *
        (∏ j ∈ Finset.range (⟨d⟩ : Fin r ⇀ ℕ)[i], ((Nat.factorial j) : ℂ)) *
        (⟨x⟩ : Fin r ⇀ ℂ)[i] ^ (⟨d⟩ : Fin r ⇀ ℕ)[i].choose 2) =
      Vand * Fact * Q := by
    simp only [Vand, Fact, Q]
    simp_rw [mul_assoc]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hL : Mmono.det = Vand * Fact * Q := by
    have hmat :
      Mmono =
          [i < n, j < n]
            ∑ k : Fin r,
              if (i : ℕ) ∈ Finset.Ico
                (∑ t ∈ Finset.Iio k, (⟨d⟩ : Fin r ⇀ ℕ)[t])
                  (∑ t ∈ Finset.Iic k, (⟨d⟩ : Fin r ⇀ ℕ)[t]) then
                (j : ℂ) ^ (i - ∑ t ∈ Finset.Iio k, (⟨d⟩ : Fin r ⇀ ℕ)[t]) *
                  (⟨x⟩ : Fin r ⇀ ℂ)[k] ^ (j : ℕ)
              else 0 := by
      ext i j
      simp [Mmono]
    rw [hmat]
    rw [hlem, hsplit]
  calc
    _ = Φ.det * Q := by rw [← hΦ]
    _ = Ψ.det := by rw [← hTdet, ← hΨdet]
    _ = Mmono.det := by rw [htrans, Matrix.det_transpose]
    _ = Vand * Fact * Q := hL

private lemma falling_det_mul
  {r n : ℕ}
  (x : Fin r → ℂ)
  (d : Fin r → ℕ)
  (hsum : ∑ k : Fin r, d k = n) :
  (Matrix.of fun (t i : Fin n) =>
    ∑ k : Fin r,
      if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
        (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
          x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
      else 0).det =
  ∏ k : Fin r, ((∏ j ∈ Finset.Iio k, (x k - x j) ^ (d k * d j)) *
    (∏ j ∈ Finset.range (d k), ((Nat.factorial j) : ℂ))) := by
  classical
  let subst (a : ℂ) : ℂ[X] := if a = 0 then X else C a
  let Vand : ℂ[X] :=
    ∏ i : Fin r, ∏ j ∈ Finset.Iio i, (subst (x i) - subst (x j)) ^ (d i * d j)
  let Fact : ℂ := ∏ i : Fin r, ∏ j ∈ Finset.range (d i), (Nat.factorial j)
  let Qp : ℂ[X] := ∏ i : Fin r, subst (x i) ^ (d i).choose 2
  let Mp : Matrix (Fin n) (Fin n) ℂ[X] :=
    Matrix.of fun t i =>
      ∑ k : Fin r,
        if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
          C (((t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) : ℂ)) *
            subst (x k) ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
        else 0
  have hQ : Qp ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i _
    refine pow_ne_zero _ ?_
    if h0 : x i = 0 then
      simp [subst, h0, X_ne_zero]
    else
      simp [subst, h0, C_ne_zero.mpr h0]
  have hprod : (Mp.det - Vand * C Fact) * Qp = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro t
    let y : Fin r → ℂ := fun k => if x k = 0 then t else x k
    have hy := falling_det_mul_Q y d hsum
    have hsubst (a : ℂ) : eval t (subst a) = if a = 0 then t else a := by
      if h0 : a = 0 then
        simp [subst, h0]
      else
        simp [subst, h0]
    have hMy :
      eval t Mp.det =
          (Matrix.of fun (time slot : Fin n) =>
            ∑ k : Fin r,
              if (slot : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
                (time : ℕ).descFactorial ((slot : ℕ) - ∑ j ∈ Finset.Iio k, d j) *
                  y k ^ ((time : ℕ) - ((slot : ℕ) - ∑ j ∈ Finset.Iio k, d j))
              else 0).det := by
      rw [← coe_evalRingHom, RingHom.map_det]
      congr 1
      ext time slot
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp only [Mp, Matrix.of_apply]
      rw [map_sum (Polynomial.evalRingHom t)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [congrFun (coe_evalRingHom t), apply_ite (eval t)]
      split_ifs with hk
      · simp only [eval_mul, eval_C, eval_pow, hsubst, y]
      · simp
    have hV : eval t Vand =
        ∏ i : Fin r, ∏ j ∈ Finset.Iio i, (y i - y j) ^ (d i * d j) := by
      simp only [Vand, eval_prod, eval_pow, eval_sub, hsubst, y]
    have hQp : eval t Qp = ∏ i : Fin r, y i ^ (d i).choose 2 := by
      simp only [Qp, eval_prod, eval_pow, hsubst, y]
    rw [eval_mul, eval_sub, eval_mul, eval_C, hMy, hV, hQp]
    have hy0 : ((Matrix.of fun (time slot : Fin n) =>
        ∑ k : Fin r,
          if (slot : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
            (time : ℕ).descFactorial ((slot : ℕ) - ∑ j ∈ Finset.Iio k, d j) *
              y k ^ ((time : ℕ) - ((slot : ℕ) - ∑ j ∈ Finset.Iio k, d j))
          else 0).det -
        (∏ i : Fin r, ∏ j ∈ Finset.Iio i, (y i - y j) ^ (d i * d j)) * Fact) *
        (∏ i : Fin r, y i ^ (d i).choose 2) = 0 := by
      rw [sub_mul, hy]
      ring
    simpa [Fact] using hy0
  have hdiff : Mp.det - Vand * C Fact = 0 := (mul_eq_zero.mp hprod).resolve_right hQ
  have hpoly : Mp.det = Vand * C Fact := by
    rwa [← sub_eq_zero]
  have hAt0 : eval 0 Mp.det =
      (Matrix.of fun (t i : Fin n) =>
        ∑ k : Fin r,
          if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
            (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
              x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
          else 0).det := by
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext time slot
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [Mp, Matrix.of_apply]
    rw [map_sum (Polynomial.evalRingHom (0 : ℂ))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsubst0 (a : ℂ) : eval 0 (subst a) = a := by
      if h0 : a = 0 then
        simp [subst, h0]
      else
        simp [subst, h0]
    rw [congrFun (coe_evalRingHom (0 : ℂ)), apply_ite (eval (0 : ℂ))]
    split_ifs with hk
    · simp only [eval_mul, eval_C, eval_pow, hsubst0]
    · simp
  rw [hpoly, eval_mul, eval_C] at hAt0
  have hV0 : eval 0 Vand = ∏ i : Fin r, ∏ j ∈ Finset.Iio i, (x i - x j) ^ (d i * d j) := by
    have hsubst0 (a : ℂ) : eval 0 (subst a) = a := by
      if h0 : a = 0 then
        simp [subst, h0]
      else
        simp [subst, h0]
    simp only [Vand, eval_prod, eval_pow, eval_sub, hsubst0]
  rw [hV0] at hAt0
  rw [prod_mul_distrib]
  apply hAt0.symm

private lemma falling_det_ne_zero
  {r n : ℕ}
  (x : Fin r → ℂ)
  (d : Fin r → ℕ)
  (hdist : ∀ i j : Fin r, i ≠ j → x i ≠ x j)
  (hsum : ∑ k : Fin r, d k = n) :
  (Matrix.of fun (t i : Fin n) =>
    ∑ k : Fin r,
      if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
        (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
          x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
      else 0).det ≠ 0 := by
  rw [falling_det_mul x d hsum]
  refine prod_ne_zero_iff.mpr ?_
  intro k _
  apply mul_ne_zero
  ·
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    apply hdist k j
    apply Ne.symm
    apply ne_of_lt
    simpa [mem_Iio] using hj
  ·
    refine prod_ne_zero_iff.mpr ?_
    intro j _
    apply Nat.cast_ne_zero.mpr
    apply Nat.factorial_ne_zero

/--
Closed form of a homogeneous linear recurrence of order `n` over `ℂ`:
`h[k + n] = c @ h[k: k + n]`. A root of multiplicity `m` contributes the
falling factorials of exponents `0, …, m - 1`, so a repeated root `0` still
frees the initial values.
-/
@[path]
private lemma main
  {n : ℕ}
  {h : ℕ ⇀ ℂ}
  {c : Fin n ⇀ ℂ}
-- given
  (hrec : ∀ k : ℕ, h[k + n] = c @ h[k: k + n]) :
-- imply
  ∃ (e : Fin n ⇀ ℕ) (r : Fin n ⇀ ℂ) (A : Fin n ⇀ ℂ), ∀ t : ℕ,
    h[t] = A @ fun i => t.descFactorial e[i] * r[i] ^ (t - e[i]) := by
-- proof
  classical
  let E : LinearRecurrence ℂ := ⟨n, fun i => c[i]⟩
  let p : ℂ[X] := E.charPoly
  have hpdeg : p.natDegree = n := by
    simpa [p, E] using natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order
  have hpmonic : p.Monic := by
    simpa [p] using E.charPoly_monic
  obtain ⟨rlin, hfactor⟩ := Any_Eq_Prod_SubXC.of.EqNatDegree.Monic hpmonic hpdeg
  let firsts : Finset (Fin n) :=
    Finset.univ.filter fun i => ∀ j : Fin n, j.val < i.val → rlin j ≠ rlin i
  let rd := firsts.card
  let iso := firsts.orderIsoOfFin (rfl : firsts.card = rd)
  let idx (k : Fin rd) : Fin n := iso k
  let x (k : Fin rd) : ℂ := rlin (idx k)
  let d (k : Fin rd) : ℕ := (Finset.univ.filter fun i => rlin i = x k).card
  have hdist : ∀ a b : Fin rd, a ≠ b → x a ≠ x b := by
    intro a b hab hx
    have hidx : idx a ≠ idx b := by
      intro h
      apply hab
      apply iso.injective
      exact Subtype.ext h
    obtain hlt | hlt := lt_or_gt_of_ne hidx
    ·
      have hb := (iso b).2
      simp only [firsts, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact hb (idx a) (Fin.lt_def.mp hlt) hx
    ·
      have ha := (iso a).2
      simp only [firsts, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ha (idx b) (Fin.lt_def.mp hlt) hx.symm
  have hsum : ∑ k : Fin rd, d k = n := by
    have hdisj (a b : Fin rd) (hab : a ≠ b) :
      Disjoint (Finset.univ.filter fun i => rlin i = x a)
          (Finset.univ.filter fun i => rlin i = x b) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
      exact hdist a b hab (hi.symm.trans hi')
    have hunion :
      (Finset.univ.biUnion fun k : Fin rd => Finset.univ.filter fun i => rlin i = x k) =
          Finset.univ := by
      ext i
      constructor
      ·
        intro
        exact Finset.mem_univ _
      ·
        intro
        rw [Finset.mem_biUnion]
        let js := Finset.univ.filter fun j : Fin n => rlin j = rlin i
        have hjs : js.Nonempty := ⟨i, by simp [js]⟩
        let j := js.min' hjs
        have hjmem : j ∈ js := Finset.min'_mem js hjs
        have hjval : rlin j = rlin i := by
          simp only [js, Finset.mem_filter] at hjmem
          exact hjmem.2
        have hjfirst : j ∈ firsts := by
          simp only [firsts, Finset.mem_filter, Finset.mem_univ, true_and]
          intro j' hlt heq
          have hj' : j' ∈ js := by
            simp only [js, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [heq, hjval]
          have hle := Finset.min'_le js j' hj'
          have hlej : (j : ℕ) ≤ j' := Fin.le_def.mp hle
          omega
        let k : Fin rd := iso.symm ⟨j, hjfirst⟩
        have hidx : idx k = j := by
          have : iso k = ⟨j, hjfirst⟩ := by
            simp [k]
          simpa only [idx] using congrArg Subtype.val this
        refine ⟨k, Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, hidx, hjval]
    have hcard :=
      Finset.card_biUnion (s := (Finset.univ : Finset (Fin rd)))
        (t := fun k => Finset.univ.filter fun i => rlin i = x k)
        (fun a _ b _ hab => hdisj a b hab)
    rw [hunion] at hcard
    simpa [d, Finset.card_univ] using hcard.symm
  have hdet := falling_det_ne_zero x d hdist hsum
  have hblock (i : Fin n) :
    ∃ k : Fin rd, (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) := by
    have hsumd : ∑ k : Fin rd, (Fun.mk d)[k] = n := by
      simpa [Fun.getElem_eq] using hsum
    obtain ⟨k, hk⟩ := Any_In_Ico_SumIioSumIic.of.Eq_Sum hsumd i
    refine ⟨k, ?_⟩
    dsimp only [GetElem.getElem] at hk
    apply hk
  let block (i : Fin n) : Fin rd := Classical.choose (hblock i)
  let ex (i : Fin n) : ℕ :=
    i - ∑ j ∈ Finset.Iio (block i), d j
  have hspec (i : Fin n) := Classical.choose_spec (hblock i)
  have hexlt (i : Fin n) : ex i < d (block i) := by
    have hi := hspec i
    simp only [Finset.mem_Ico] at hi
    have hle : ∑ j ∈ Finset.Iio (block i), d j ≤ i := by
      simpa [block] using hi.1
    have hlt : i < ∑ j ∈ Finset.Iio (block i), d j + d (block i) := by
      have h := AddSumIio.eq.SumIic (Fun.mk d) (block i)
      dsimp only [GetElem.getElem] at h
      rw [h]
      simpa [block] using hi.2
    simp only [ex]
    exact (Nat.sub_lt_iff_lt_add' hle).mpr hlt
  let root (i : Fin n) : ℂ := x (block i)
  let basis (i : Fin n) (t : ℕ) : ℂ :=
    t.descFactorial (ex i) * root i ^ (t - ex i)
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun t i => basis i t
  have hM : M.det ≠ 0 := by
    have hEq : M =
        Matrix.of fun (t i : Fin n) =>
          ∑ k : Fin rd,
            if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
              (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
                x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
            else 0 := by
      ext t i
      simp only [M, Matrix.of_apply, basis, root]
      rw [Finset.sum_eq_single_of_mem (block i) (Finset.mem_univ _)]
      ·
        have hi := hspec i
        rw [ite_eq_left hi]
      ·
        intro k' _ hk'
        have hnot :
          (i : ℕ) ∉ Finset.Ico (∑ j ∈ Finset.Iio k', d j) (∑ j ∈ Finset.Iic k', d j) := by
          intro hkmem
          apply hk'
          refine Eq.of.In_Ico_SumIioSumIic.In_Ico_SumIioSumIic
            (d := Fun.mk d) (t := i) (k₁ := k') (k₂ := block i) ?_ ?_
          ·
            dsimp only [GetElem.getElem]
            apply hkmem
          ·
            dsimp only [GetElem.getElem]
            apply hspec i
        simp [hnot]
    simpa [hEq] using hdet
  let bvec : Fin n → ℂ := fun i => h[i]
  let cvec : Fin n → ℂ := Matrix.mulVec M⁻¹ bvec
  have hMc : Matrix.mulVec M cvec = bvec := by
    rw [show cvec = Matrix.mulVec M⁻¹ bvec from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  have hrow (i : Fin n) :
    h[i] = ∑ s : Fin n, cvec s * basis s i := by
    have hsumv := congr_fun hMc i
    rw [Matrix.mulVec_apply_eq_sum] at hsumv
    calc
      _ = bvec i := by simp [bvec]
      _ = ∑ s : Fin n, M i s * cvec s := by rw [← hsumv]
      _ = ∑ s : Fin n, cvec s * basis s i := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp [M]
        ring
  have hbasis (s : Fin n) : E.IsSolution (basis s) := by
    intro m
    let ρ : ℂ := root s
    let e : ℕ := ex s
    have he : e < p.rootMultiplicity ρ := by
      rw [hfactor, rootMultiplicity_prod_linear]
      simpa [d, ρ, root, e] using hexlt s
    have hp0 : p ≠ 0 := hpmonic.ne_zero
    have hshift : X ^ m * p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hp0
    have hmult : e < (X ^ m * p).rootMultiplicity ρ := by
      rw [rootMultiplicity_mul hshift]
      omega
    have hzero : (Nat.iterate derivative e (X ^ m * p)).eval ρ = 0 := by
      simpa [IsRoot] using isRoot_iterate_derivative_of_lt_rootMultiplicity hmult
    have hpX : p = X ^ n - ∑ i : Fin n, C c[i] * X ^ (i : ℕ) := by
      simp only [p, LinearRecurrence.charPoly, E]
      simp_rw [← C_mul_X_pow_eq_monomial]
      simp
    have hq : X ^ m * p =
        X ^ (m + n) - ∑ i : Fin n, C c[i] * X ^ (m + i) := by
      rw [hpX, mul_sub, Finset.mul_sum]
      congr 1
      · rw [← pow_add]
      ·
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    have hderiv : Nat.iterate derivative e (X ^ m * p) =
        C (((m + n).descFactorial e : ℂ)) * X ^ ((m + n) - e) -
          ∑ i : Fin n, C c[i] *
            (C (((m + i).descFactorial e : ℂ)) * X ^ ((m + i) - e)) := by
      rw [hq, iterate_derivative_sub, iterate_derivative_sum]
      simp_rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul]
    rw [hderiv, eval_sub] at hzero
    have hpush (f : Fin n → ℂ[X]) : eval ρ (∑ i, f i) = ∑ i, eval ρ (f i) :=
      map_sum (evalRingHom ρ) f Finset.univ
    rw [hpush] at hzero
    simp only [eval_mul, eval_C, eval_pow, eval_X] at hzero
    rw [sub_eq_zero] at hzero
    simpa [basis, ρ, root, e, E, mul_assoc] using hzero
  let u : ℕ → ℂ := fun t => ∑ s : Fin n, cvec s * basis s t
  have hcombo : E.IsSolution u := by
    intro m
    show u (m + n) = ∑ i : Fin n, E.coeffs i * u (m + i)
    calc
      _ = ∑ s : Fin n, cvec s * basis s (m + n) := by simp [u]
      _ = ∑ s : Fin n, cvec s * ∑ i : Fin n, E.coeffs i * basis s (m + i) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hbasis s m]
      _ = ∑ s : Fin n, ∑ i : Fin n, cvec s * (E.coeffs i * basis s (m + i)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ i : Fin n, ∑ s : Fin n, cvec s * E.coeffs i * basis s (m + i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
        ring
      _ = ∑ i : Fin n, E.coeffs i * ∑ s : Fin n, cvec s * basis s (m + i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      _ = ∑ i : Fin n, E.coeffs i * u (m + i) := by simp [u]
  have hEsol : E.IsSolution (fun t => h[t]) := by
    intro k
    simpa [E, LinearRecurrence.IsSolution, Dot.fun_getSlice_eq] using hrec k
  have hagree : Set.EqOn (fun t => h[t]) u ↑(Finset.range n) := by
    intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    simpa [u] using hrow ⟨t, ht⟩
  have hu : (fun t => h[t]) = u :=
    (E.eq_iff_eqOn_range_order (fun t => h[t]) u hEsol hcombo).mpr hagree
  refine ⟨⟨ex⟩, ⟨root⟩, ⟨cvec⟩, ?_⟩
  intro t
  simpa [u, basis, Fun.getElem_eq, Dot.fun_fin_eq] using congr_fun hu t


-- created on 2026-10-25
