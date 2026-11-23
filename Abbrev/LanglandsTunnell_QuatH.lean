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

abbrev fixFld (H : Subgroup (L ≃ₐ[ℚ] L)) : IntermediateField ℚ L :=
  FixedPoints.intermediateField (↥H)


section SynthProbe

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))

end SynthProbe

end LanglandsTunnell
