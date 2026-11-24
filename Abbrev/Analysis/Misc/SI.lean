module
public import Mathlib
public import Theorem.Analysis.Misc.UnitsSystem.Part23
public import Mathlib.Algebra.Group.MinimalAxioms
public import Instance.Analysis.Misc.SI.Part3


public section

abbrev SI : UnitsSystem := {
  Dimensions := SI_dimensions
  addCommGroup := SI_dimensions.instAddCommGroup
}

