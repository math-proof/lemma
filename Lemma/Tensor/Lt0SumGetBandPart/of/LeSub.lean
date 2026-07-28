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
-- given
  (m l u : ℕ)
  (i : Fin m)
  (h : i ≤ n - 1 + l) :
-- imply
  (((1 : Tensor α [m, n]).band_part l u).get i).sum > 0 := by
-- proof
  let j : Fin n :=
    if hlt : i.val < n then ⟨i.val, hlt⟩ else ⟨n - 1, Nat.pred_lt (NeZero.ne n)⟩
  have hband : (j - i : ℤ) ∈ Icc (-l : ℤ) u := by
    obtain hi | hi := Nat.lt_or_ge i.val n
    · simp only [j, hi, dite_true, Set.mem_Icc, Fin.val_mk]
      constructor <;> linarith
    · have hjn : j = ⟨n - 1, Nat.pred_lt (NeZero.ne n)⟩ := by
        dsimp [j]
        split_ifs
        · exact absurd ‹_› (Nat.not_lt.mpr hi)
        · rfl
      rw [hjn, Set.mem_Icc, Fin.val_mk]
      omega
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have h_icc :
      ⌈((↑(i - l) : ℤ) - ((i : ℤ) - l)) / (1 : ℚ)⌉ ≤
        ⌊((↑((n - 1) ⊓ (i + u)) : ℤ) - ((i : ℤ) - l)) / (1 : ℚ)⌋ :=
    LeCeil_Floor.of.Any_And_Dvd_AddSub (l := l) (u := u) (i := ↑i) ⟨j, hband, one_dvd _⟩
  exact Lt0SumGetBandPart.of.LeCeil_Floor (m := m) (l := l) (u := u) (i := i) (d := 1) h_icc


-- created on 2026-07-28
