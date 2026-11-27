module

public import Mathlib
public import Def.ModularForm_HeckeOperator

public section

namespace ModularFormClass

axiom isBoundedAt_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsBoundedAt c (ModularForm.heckeT k p ⇑f) k

end ModularFormClass
