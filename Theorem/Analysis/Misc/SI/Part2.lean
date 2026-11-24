module
public import Mathlib
public import Theorem.Analysis.Misc.UnitsSystem.Part23
public import Mathlib.Algebra.Group.MinimalAxioms
public import Instance.Analysis.Misc.SI.Part2


public section

@[simp]
theorem Rat.neg_eq (q:ℚ) : Rat.neg q = -q := rfl

theorem Rat.add_eq (q r:ℚ) : Rat.add q r = q + r := rfl

