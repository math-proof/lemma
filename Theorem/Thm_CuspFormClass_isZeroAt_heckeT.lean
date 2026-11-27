module

public import Mathlib
public import Def.ModularForm_HeckeOperator

public section

namespace CuspFormClass

axiom isZeroAt_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsZeroAt c (ModularForm.heckeT k p ⇑f) k

end CuspFormClass
