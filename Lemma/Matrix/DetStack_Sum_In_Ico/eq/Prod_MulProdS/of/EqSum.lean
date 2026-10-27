import Lemma.Finset.AddSumIio.eq.SumIic
import Lemma.Finset.Any_In_IcoSumIio_SumIic.of.Eq_Sum
import Lemma.Finset.Eq.of.In_IcoSumIio_SumIic.In_IcoSumIio_SumIic
import Lemma.Matrix.DetStack_Sum_Ite.eq.Prod_MulMulProdS.of.EqSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Interval.Finset.Fin
import Syntax.LinearAlgebra.Matrix.Notation
import Theorem.Function
open Polynomial Matrix Finset
set_option maxHeartbeats 999999


private lemma falling_det_mul_Q
  {r n : ℕ}
  {x : Fin r → ℂ}
  {d : Fin r → ℕ}
-- given
  (hsum : ∑ k : Fin r, d k = n) :
-- imply
  ([t < n, i < n]
    ∑ k : Fin r,
      if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
        (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
          x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
      else 0).det *
    (∏ k : Fin r, x k ^ (d k).choose 2) =
  (∏ k : Fin r, ∏ j ∈ Finset.Iio k, (x k - x j) ^ (d k * d j)) *
    (∏ k : Fin r, ∏ j ∈ Finset.range (d k), ((Nat.factorial j) : ℂ)) *
    (∏ k : Fin r, x k ^ (d k).choose 2) := by
-- proof
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
      refine Eq.of.In_IcoSumIio_SumIic.In_IcoSumIio_SumIic
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
        obtain ⟨k, hk⟩ := Any_In_IcoSumIio_SumIic.of.Eq_Sum hsumd i
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
    [t < n, i < n]
      (t : ℕ).descFactorial (ex i) * x (block i) ^ ((t : ℕ) - ex i)
  let Ψ : Matrix (Fin n) (Fin n) ℂ :=
    [t < n, i < n] ((t : ℕ) : ℂ) ^ ex i * x (block i) ^ (t : ℕ)
  let T : Matrix (Fin n) (Fin n) ℂ :=
    [s < n, i < n]
      if block s = block i ∧ ex s ≤ ex i then
        Nat.stirlingSecond (ex i) (ex s) * x (block i) ^ ex s
      else 0
  have hΦ : Φ =
      [t < n, i < n]
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
        refine Eq.of.In_IcoSumIio_SumIic.In_IcoSumIio_SumIic
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
    [i < n, j < n]
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
        refine Eq.of.In_IcoSumIio_SumIic.In_IcoSumIio_SumIic
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

@[path]
private lemma main
  {r n : ℕ}
  {x : Fin r → ℂ}
  {d : Fin r → ℕ}
-- given
  (hsum : ∑ k : Fin r, d k = n) :
-- imply
  ([t < n, i < n]
    ∑ k : Fin r,
      if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
        (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
          x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
      else 0).det =
  ∏ k : Fin r, ((∏ j ∈ Finset.Iio k, (x k - x j) ^ (d k * d j)) *
    (∏ j ∈ Finset.range (d k), ((Nat.factorial j) : ℂ))) := by
-- proof
  classical
  let subst (a : ℂ) : ℂ[X] := if a = 0 then X else C a
  let Vand : ℂ[X] :=
    ∏ i : Fin r, ∏ j ∈ Finset.Iio i, (subst (x i) - subst (x j)) ^ (d i * d j)
  let Fact : ℂ := ∏ i : Fin r, ∏ j ∈ Finset.range (d i), (Nat.factorial j)
  let Qp : ℂ[X] := ∏ i : Fin r, subst (x i) ^ (d i).choose 2
  let Mp : Matrix (Fin n) (Fin n) ℂ[X] :=
    [t < n, i < n]
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
    have hy := falling_det_mul_Q (x := y) hsum
    have hsubst (a : ℂ) : eval t (subst a) = if a = 0 then t else a := by
      if h0 : a = 0 then
        simp [subst, h0]
      else
        simp [subst, h0]
    have hMy :
      eval t Mp.det =
          ([time < n, slot < n]
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
    have hy0 : (([time < n, slot < n]
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
      ([t < n, i < n]
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


-- created on 2026-10-25
