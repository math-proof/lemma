/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean -/


import sympy.atlas.Combinatorics.JaccardLattice
import Lemma.Finset.JaccardLattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace JaccardLatticeTest

open JaccardLattice

/-- Shifted counting valuation on `ℕ` for compile-time checks. -/
private noncomputable def countVal : ℕ → ℝ := fun n => (n : ℝ) + 1

example : 0 < jaccardDist countVal 0 1 := by
  rw [countVal_01]
  norm_num

example : jaccardDist countVal 0 1 + jaccardDist countVal 1 2
    ≥ jaccardDist countVal 0 2 :=
  jaccardDist_triangle countVal_mod countVal_mono countVal_pos 0 2 1

example : jaccardDist countVal 0 1 + jaccardDist countVal 1 2
    > jaccardDist countVal 0 2 := by
  rw [countVal_01, countVal_12, countVal_02]
  norm_num

end JaccardLatticeTest
