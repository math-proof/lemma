module
public import Def.LanglandsTunnell_ExplicitLift
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Theorem.Matrix.Lift48
public import Def.Matrix_Lift48
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_LanglandsTunnell_Lift48.lean: instance decls only.

namespace LanglandsTunnell.Lift48

open FLT.ExplicitLift Matrix


instance : DecidablePred IsPM1 := fun A => inferInstanceAs (Decidable (A = 1 ∨ A = -1))

instance (n : ℕ) : DecidablePred (IsProjOrder n) := fun A =>
  inferInstanceAs (Decidable (IsPM1 (pw A n) ∧ ∀ m ∈ List.range' 1 (n - 1), ¬ IsPM1 (pw A m)))


end LanglandsTunnell.Lift48
