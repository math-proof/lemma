module
public import Def.LanglandsTunnell_C8Character
public import Instance.LanglandsTunnell_QuatH
public import Instance.LanglandsTunnell_C8Tower
set_option autoImplicit false


public section

namespace LanglandsTunnell


private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private noncomputable def redUnit (M : {M : Lift48.Mat // M ∈ Lift48.P16}) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.1.map FLT.ExplicitLift.red) (det_map_red_ne_zero M.1 M.2)

section Card

variable {L : Type} [Field L] [NumberField L]

private noncomputable def toSylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Lift48.Mat // M ∈ Lift48.P16}) : ↥(sylowH e) :=
  ⟨e.symm (redUnit M), M.1, M.2, by rw [MulEquiv.apply_symm_apply, coe_redUnit]⟩

end Card


end LanglandsTunnell
