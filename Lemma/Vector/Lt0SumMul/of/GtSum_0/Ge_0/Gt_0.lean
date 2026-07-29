import Lemma.Finset.GtSumS.of.Any_Gt.All_Ge
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.Le0Mul.of.Ge_0.Ge_0
import Lemma.Vector.Sum.eq.Sum_Get
import sympy.vector.vector
open Finset Nat Vector


@[main]
private lemma main
  [Semiring α] [PartialOrder α] [IsOrderedCancelAddMonoid α] [PosMulStrictMono α]
  {X Y : List.Vector α n}
-- given
  (h_X : X > 0)
  (h_Y : Y ≥ 0)
  (h_sum : Y.sum > 0) :
-- imply
  (X * Y).sum > 0 := by
-- proof
  have h_X_pos : ∀ i : Fin n, (0 : List.Vector α n)[i] < X[i] := by
    intro i
    exact h_X i
  have h_X_ge : X ≥ 0 := by
    intro i
    exact le_of_lt (h_X_pos i)
  have h_XY_ge := Le0Mul.of.Ge_0.Ge_0 h_X_ge h_Y
  have h_Yfin : ∑ k : Fin n, Y[k] > 0 := by rwa [← Sum.eq.Sum_Get]
  have h_gt : ∃ k : Fin n, (X * Y)[k] > 0 := by
    by_contra hall
    have hY0 : ∀ k : Fin n, Y[k] = 0 := by
      intro k
      have hXYk_ge : 0 ≤ (X * Y)[k] := by simpa [GetElem.getElem, EqGet0_0.fin] using h_XY_ge k
      have hXYk_le : (X * Y)[k] ≤ 0 := by obtain heq | hpos := eq_or_lt_of_le hXYk_ge <;> grind
      have hXYk := le_antisymm hXYk_le hXYk_ge
      have hXYprod : (X * Y)[k] = X[k] * Y[k] := GetMul.eq.MulGetS X Y k
      rw [hXYprod] at hXYk
      have hXk : 0 < X[k] := by
        have hlt := h_X_pos k
        rwa [show (0 : List.Vector α n)[k] = 0 by simpa [GetElem.getElem] using EqGet0_0.fin k] at hlt
      have hYk : 0 ≤ Y[k] := by
        have := h_Y k
        simp [GetElem.getElem, EqGet0_0.fin] at this
        simpa
      obtain hYeq | hYgt := eq_or_lt_of_le hYk
      ·
        aesop
      ·
        grind [Nat.Lt0Mul.of.Gt_0.Gt_0 hXk hYgt, GetMul.eq.MulGetS X Y k]
    apply ne_of_gt h_Yfin
    apply Finset.sum_eq_zero fun k _ => hY0 k
  obtain ⟨k, hk⟩ := h_gt
  rw [Sum.eq.Sum_Get]
  have hpos := GtSumS.of.Any_Gt.All_Ge
    (x := fun i => (X * Y)[i])
    (y := fun _ => 0)
    (fun i _ => by simpa [GetElem.getElem, EqGet0_0.fin] using h_XY_ge i)
    ⟨k, mem_univ k, hk⟩
  rwa [Finset.sum_const_zero] at hpos


-- created on 2026-07-29
