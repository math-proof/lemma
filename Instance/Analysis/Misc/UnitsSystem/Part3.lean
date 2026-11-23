module

public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part4
@[expose] public section

set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- In the next few lines of code we give {lean}`Scalar d` the structure of a real vector space,
which is of course compatible with the real vector space structure on {name}`Formal`.  -/
instance Scalar.instAdd {d:Dimensions} : Add (Scalar d) where
  add q₁ q₂ := ⟨q₁.val + q₂.val⟩

end UnitsSystem
