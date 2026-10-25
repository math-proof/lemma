import Mathlib
import Theorem.Analysis.Misc.UnitsSystem.Part23
import Mathlib.Algebra.Group.MinimalAxioms
import Abbrev.Analysis.Misc.SI


/-- The SI system will be automatically installed as a global instance by any Lean file that imports this one.  This makes it difficult to use any competing {name}`UnitsSystem`
simultaneously, but that should be a rare use case. -/
instance instSI : UnitsSystem := SI

instance instSI_module : Module ℚ SI.Dimensions := SI_dimensions.instModule

