module
public import Mathlib
public import Theorem.Analysis.Misc.UnitsSystem.Part23
public import Mathlib.Algebra.Group.MinimalAxioms
public import Structure.Analysis.Misc.SI


public section

instance SI_dimensions.instZero : Zero SI_dimensions where
  zero := ⟨0, 0, 0, 0, 0, 0, 0⟩

