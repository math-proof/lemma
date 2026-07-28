import Lemma.Rat.LeCeil_Floor.is.Any_And_Dvd_AddSub
import Lemma.Tensor.Lt0SumGetBandPart.of.LeCeil_Floor
import sympy.matrices.expressions.special
import sympy.sets.sets
open Rat Tensor


@[main]
private lemma main
  [AddCommMonoidWithOne α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [IsOrderedCancelAddMonoid α]
  [NeZero (1 : α)]
  [NeZero n]
  {i : Fin m}
-- given
  (h : i.val ≤ n - 1 + l) :
-- imply
  (((1 : Tensor α [m, n]).band_part l u).get i).sum > 0 := by
-- proof
  let j : Fin n := if hlt : i.val < n then ⟨i.val, hlt⟩ else ⟨n - 1, Nat.pred_lt (NeZero.ne n)⟩
  have hband : (j - i : ℤ) ∈ Icc (-l : ℤ) u := by
    obtain hi | hi := Nat.lt_or_ge i.val n
    ·
      simp only [j, hi, dite_true, Set.mem_Icc, Fin.val_mk]
      constructor <;>
        linarith
    ·
      have hjn : j = ⟨n - 1, Nat.pred_lt (NeZero.ne n)⟩ := by
        dsimp [j]
        split_ifs
        ·
          grind
        ·
          rfl
      rw [hjn, Set.mem_Icc, Fin.val_mk]
      omega
  apply Lt0SumGetBandPart.of.LeCeil_Floor
  apply LeCeil_Floor.of.Any_And_Dvd_AddSub ⟨j, hband, one_dvd _⟩


-- created on 2026-07-28
