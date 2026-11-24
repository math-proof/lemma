module
public import Def.LanglandsTunnell_CubicInduction_ArchSmoothSpace3
public import Instance.LanglandsTunnell_CubicInduction_EnvelopingAction3
public import Abbrev.LanglandsTunnell_CubicInduction_EnvelopingAction3
set_option autoImplicit false


public section

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LanglandsTunnell.CubicInduction.WhittakerBlock

def derivAction3 : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ smoothFunctions3 :=
  (Matrix.stdBasis ℂ (Fin 3) (Fin 3)).constr ℂ fun p => archDerivₗ p.1 p.2

private def rightFieldLin (A : Matrix (Fin 3) (Fin 3) ℝ) : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ) where
  toFun e := fun a b => ∑ c, e a c * A c b
  map_add' e e' := by
    funext a b
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r e := by
    funext a b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

private def rightFieldCLM (A : Matrix (Fin 3) (Fin 3) ℝ) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap (rightFieldLin A)

private def rightField (A : Matrix (Fin 3) (Fin 3) ℝ) (F : (Fin 3 → Fin 3 → ℝ) → ℂ) (e : Fin 3 → Fin 3 → ℝ) : ℂ :=
  fderiv ℝ F e (rightFieldCLM A e)

def derivLieHom3 : Matrix (Fin 3) (Fin 3) ℂ →ₗ⁅ℂ⁆ Module.End ℂ smoothFunctions3 :=
  { derivAction3 with map_lie' := fun {X Y} => derivAction3_lie X Y }

def envelopingHom3 : envelopingAlgebra3 →ₐ[ℂ] Module.End ℂ smoothFunctions3 :=
  UniversalEnvelopingAlgebra.lift ℂ derivLieHom3

abbrev envelopingModule3 : Module envelopingAlgebra3 smoothFunctions3 :=
  Module.compHom smoothFunctions3 envelopingHom3.toRingHom

end LanglandsTunnell.CubicInduction.WhittakerBlock

end
