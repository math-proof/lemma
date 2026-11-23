module

public import Theorem.Matrix.SylowH
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField FLT.ExplicitLift LanglandsTunnell.Lift48
open scoped MatrixGroups

variable {L : Type} [Field L] [NumberField L]


def detKer (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : Subgroup (L ≃ₐ[ℚ] L) :=
  (Matrix.GeneralLinearGroup.det.comp e.toMonoidHom).ker


def quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : Subgroup (L ≃ₐ[ℚ] L) :=
  sylowH e ⊓ detKer e

end LanglandsTunnell
