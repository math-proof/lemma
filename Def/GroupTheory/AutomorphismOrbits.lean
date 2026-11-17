/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AutomorphismOrbits.lean -/

module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Defs

@[expose] public section

namespace MetaMathlibExt

/-- The full automorphism group has finitely many orbits on the elements of the group. -/
def HasFinitelyManyAutomorphismOrbits (G : Type*) [Group G] : Prop :=
  Finite (MulAction.orbitRel.Quotient (MulAut G) G)

end MetaMathlibExt
