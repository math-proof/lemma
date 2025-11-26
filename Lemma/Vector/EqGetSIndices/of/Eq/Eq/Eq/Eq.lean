import sympy.vector.Basic
import Lemma.Nat.CoeAdd_1.eq.AddCoe_1
import Lemma.Bool.OrOr.is.Or_Or
import Lemma.Int.LeToNatS.of.Le
import Lemma.Nat.Lt.of.Lt.Le
import Lemma.Int.EqToNat_0.of.Le_0
import Lemma.Nat.CeilDivSubMin.le.Zero.of.Le
import Lemma.Nat.Min
import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.NotLe.of.Gt
import Lemma.List.EqGetSSlicedIndices.of.GtLength.GtLength.Gt_0.Gt_0.Le.Le.Lt.Lt
import Lemma.List.EqGetSSlicedIndices'.of.GtLength.GtLength.Gt_0.Gt_0.Le.Le.Lt.Lt
open List Bool Int Nat


@[main]
private lemma main
-- given
  (h_start : start = start')
  (h_stop : stop = stop')
  (h_step : step = step')
  (h_n : n = n')
  (h_i' : i < (⟨start', stop', step'⟩ : Slice).length n')
  (h_i : i < (⟨start, stop, step⟩ : Slice).length n) :
-- imply
  (List.Vector.indices ⟨start, stop, step⟩ n)[i].val = (List.Vector.indices ⟨start', stop', step'⟩ n')[i].val := by
-- proof
  unfold List.Vector.indices
  unfold Slice.toList
  match step with
  | .ofNat step =>
    match step' with
    | .ofNat step' =>
      simp at h_step
      match step with
      | 0 =>
        simp
        match step' with
        | 0 =>
          unfold Slice.length at h_i
          simp at h_i
        | step' + 1 =>
          contradiction
      | step + 1 =>
        match step' with
        | 0 =>
          contradiction
        | step' + 1 =>
          simp
          split_ifs with h
          ·
            simp at h_i
            unfold Slice.length at h_i
            rw [AddCoe_1.eq.CoeAdd_1] at h_i
            simp at h_i
            rw [OrOr.is.Or_Or] at h
            rcases h with h | h | h
            ·
              have h := LeToNatS.of.Le h
              have h := CeilDivSubMin.le.Zero.of.Le h step n (α := ℚ)
              have h_i := Lt.of.Lt.Le h_i h
              contradiction
            ·
              have h := EqToNat_0.of.Le_0 h
              have h_ge : (Slice.Add_Mul_DivSub1Sign_2 n start).toNat ≥ 0 := by simp
              rw [← h] at h_ge
              have h := CeilDivSubMin.le.Zero.of.Le h_ge step n (α := ℚ)
              have h_i := Lt.of.Lt.Le h_i h
              contradiction
            ·
              have h := CeilDivSubMin.le.Zero.of.Le h step (Slice.Add_Mul_DivSub1Sign_2 n stop).toNat (α := ℚ)
              rw [Min.comm] at h
              have h_i := Lt.of.Lt.Le h_i h
              contradiction
          ·
            simp [GetElem.getElem]
            simp [List.Vector.get]
            rw [h_n, h_stop, h_start] at h
            simp at h
            let ⟨⟨h_lt, h_stop'⟩, h_start'⟩ := h
            have h_lt := NotLe.of.Gt h_lt
            have h_stop' := NotLe.of.Gt h_stop'
            have h_start' := NotLe.of.Gt h_start'
            simp [h_lt, h_stop', h_start']
            apply EqGetSSlicedIndices.of.GtLength.GtLength.Gt_0.Gt_0.Le.Le.Lt.Lt
            ·
              rw [h_start, h_n]
            ·
              rw [h_stop, h_n]
            ·
              simp_all
    | .negSucc step' =>
      contradiction
  | .negSucc step =>
    match step' with
    | .ofNat step' =>
      contradiction
    | .negSucc step' =>
      simp
      simp at h_step
      split_ifs with h
      ·
        unfold Slice.length at h_i
        simp at h_i
        rw [OrOr.is.Or_Or] at h
        rcases h with h | h | h
        ·
          have h := LeAddS.of.Le 1 h
          have h := LeToNatS.of.Le h
          have h := CeilDivSubMin.le.Zero.of.Le h step n (α := ℚ)
          have h_i := Lt.of.Lt.Le h_i h
          contradiction
        ·
          have h := EqToNat_0.of.Le_0 h
          have h_ge : (Slice.Add_Mul_DivSub1Sign_2 n stop + 1).toNat ≥ 0 := by simp
          rw [← h] at h_ge
          have h := CeilDivSubMin.le.Zero.of.Le h_ge step n (α := ℚ)
          have h_i := Lt.of.Lt.Le h_i h
          contradiction
        ·
          have h := CeilDivSubMin.le.Zero.of.Le h step (Slice.Add_Mul_DivSub1Sign_2 n start + 1).toNat (α := ℚ)
          rw [Min.comm] at h
          have h_i := Lt.of.Lt.Le h_i h
          contradiction
      ·
        simp [GetElem.getElem]
        simp [List.Vector.get]
        rw [h_n, h_stop, h_start] at h
        simp at h
        let ⟨⟨h_lt, h_stop'⟩, h_start'⟩ := h
        have h_lt := NotLe.of.Gt h_lt
        have h_stop' := NotLe.of.Gt h_stop'
        have h_start' := NotLe.of.Gt h_start'
        simp [h_lt, h_stop', h_start']
        apply EqGetSSlicedIndices'.of.GtLength.GtLength.Gt_0.Gt_0.Le.Le.Lt.Lt
        ·
          rw [h_start, h_n]
        ·
          rw [h_stop, h_n]
        ·
          simp_all


-- created on 2025-05-27
-- updated on 2025-05-28
