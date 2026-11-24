module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part11
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- We are finally able to view {lean}`Scalar d` as a vector space over {lean}`ℝ` as promised. -/
instance Scalar.instModule {d:Dimensions} : Module ℝ (Scalar d) where
  smul_add c q₁ q₂ := by simp [←toFormal_inj]; ring
  add_smul c1 c2 q := by simp [←toFormal_inj]; ring
  one_smul q := by simp [←toFormal_inj]
  zero_smul q := by simp [←toFormal_inj]
  mul_smul c1 c2 q := by simp [←toFormal_inj]; ring
  smul_zero c := by simp [←toFormal_inj]

end UnitsSystem
