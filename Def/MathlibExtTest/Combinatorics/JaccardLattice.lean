/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean -/


import Def.Combinatorics.JaccardLattice
import Lemma.Finset.JaccardLattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum


namespace JaccardLatticeTest

open JaccardLattice

/-- Shifted counting valuation on `ℕ` for compile-time checks. -/
noncomputable def countVal : ℕ → ℝ := fun n => (n : ℝ) + 1

end JaccardLatticeTest
