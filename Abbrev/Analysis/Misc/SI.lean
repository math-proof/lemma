import Mathlib
import Theorem.Analysis.Misc.UnitsSystem.Part23
import Mathlib.Algebra.Group.MinimalAxioms
import Instance.Analysis.Misc.SI.Part3


abbrev SI : UnitsSystem := {
  Dimensions := SI_dimensions
  addCommGroup := SI_dimensions.instAddCommGroup
}

