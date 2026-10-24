import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.NumberTheory.LSeries.AsymptoticContinuation
open Filter Asymptotics Topology


/--
[isBigO_const_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AsymptoticContinuation.lean)
-/
@[path]
the shifted partial sums vanish. -/
private lemma isBigO_const_remainder (ρ : ℂ) :
  (fun n => abelPartialSum (fun _ : ℕ => ρ) n - n • ρ) =O[atTop]
    fun n => ((n : ℝ) ^ (0 : ℝ) : ℝ) := by
  have hzero : (fun n => abelPartialSum (fun _ : ℕ => ρ) n - n • ρ) =
    fun _ => 0 := by
    funext n
    simp only [abelPartialSum, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, sub_self]
  rw [hzero]
  exact isBigO_zero _ _


-- created on 2026-10-23
