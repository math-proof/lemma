/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean -/

import Mathlib.Data.Nat.Log
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.PGroup
/-!
# Breadth of elements and finite groups

The breadth of an element `g` is the exponent `br(g)` with
`p ^ br(g) = |g^G|`, recovered as the base-`p` logarithm of the
conjugacy-class size. The breadth of a finite group is the maximum
element breadth. Every conjugacy-class size in a finite `p`-group is a
power of `p`, so the logarithm recovers the exact exponent.
-/


namespace ClassBreadth

variable {G : Type*} [Group G]

/-- The breadth of an element: the base-`p` logarithm of its conjugacy-class
size. In a finite `p`-group this is the exact exponent `br(g)` with
`p ^ br(g) = |g^G|` (see `pow_elementBreadth_eq_card`). -/
noncomputable def elementBreadth [Finite G] (p : ℕ) (g : G) : ℕ :=
  Nat.log p (Nat.card (ConjClasses.mk g).carrier)

/-- The breadth of a finite group: the maximum element breadth. -/
noncomputable def breadth (p : ℕ) (G : Type*) [Group G] [Fintype G] : ℕ :=
  Finset.univ.sup (fun g : G ↦ elementBreadth p g)

end ClassBreadth
