/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AutomorphismOrbits.lean -/

import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Defs

namespace MetaMathlibExt

/-- The full automorphism group has finitely many orbits on the elements of the group. -/
def HasFinitelyManyAutomorphismOrbits (G : Type*) [Group G] : Prop :=
  Finite (MulAction.orbitRel.Quotient (MulAut G) G)

end MetaMathlibExt
