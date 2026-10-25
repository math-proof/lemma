/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AmenableGroup.lean -/

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.PUnit
import Def.GroupTheory.AmenableGroup
open scoped Pointwise Classical symmDiff


/-- The symmetric group `S₃` is amenable (an ordinary finite example). -/
example : IsAmenable (Equiv.Perm (Fin 3)) := isAmenable_of_finite _

/-- The trivial group is amenable (a boundary example). -/
example : IsAmenable PUnit := isAmenable_of_subsingleton _

