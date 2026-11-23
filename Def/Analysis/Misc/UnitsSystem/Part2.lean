module

public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part2

@[expose] public section

set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- The existing Mathlib method {name}`AddMonoidAlgebra.single` is perfect for embedding each type of
{name}`Scalar` into the formal graded ring {name}`Formal`. -/
@[coe]
noncomputable def Scalar.toFormal {d:Dimensions} (q:Scalar d) : Formal :=
  AddMonoidAlgebra.single d q.val

end UnitsSystem
