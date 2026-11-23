/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean -/

module

public import Def.Combinatorics.JaccardLattice
public import Theorem.Finset.JaccardLattice
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace JaccardLatticeTest

open JaccardLattice

/-- Shifted counting valuation on `ℕ` for compile-time checks. -/
noncomputable def countVal : ℕ → ℝ := fun n => (n : ℝ) + 1

end JaccardLatticeTest
