module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part10
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- It is convenient to view the real numbers as a subring of the {name}`Formal` ring, thus identifying
{name}`Scalar` multiplication with ordinary multiplication. -/
noncomputable instance Formal.instCoeReal : Coe ℝ Formal where
  coe r := ((r:Scalar 0):Formal)

end UnitsSystem
