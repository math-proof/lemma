module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part13
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- Similarly, one can raise a {lean}`Scalar d` quantity to a natural number power {name}`n` to obtain a {lean}`Scalar (n • d)` quantity.  One could also implement exponentiation to an integer, but I have elected
not to do this, implementing an inversion relation instead. -/
noncomputable def Scalar.pow {d:Dimensions} (q: Scalar d) (n:ℕ) : Scalar (n • d) := ⟨ q.val^n ⟩

end UnitsSystem
