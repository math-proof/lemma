/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AmenableGroup.lean -/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.PUnit
public import Def.GroupTheory.AmenableGroup
open scoped Pointwise Classical symmDiff

public section

/-- The symmetric group `S₃` is amenable (an ordinary finite example). -/
example : IsAmenable (Equiv.Perm (Fin 3)) := isAmenable_of_finite _

/-- The trivial group is amenable (a boundary example). -/
example : IsAmenable PUnit := isAmenable_of_subsingleton _

