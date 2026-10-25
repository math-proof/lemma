import Lemma.LanglandsTunnell.CubicInduction_PrincipalSeries3
import Def.LanglandsTunnell_StandardLocalConstantsAt
import Lemma.AutomorphicForm.SmoothingKernel
import Lemma.AutomorphicForm.LocalOrbitalBase

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal

namespace LanglandsTunnell.CubicInduction

section GodementSection

variable (v : HeightOneSpectrum (𝓞 ℚ))

def setCol23 (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (j : Fin 3)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.of fun i k => if k = j then (if i = 0 then u.1 else u.2) else X i k


def setCol22 (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (j : Fin 2)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  Matrix.of fun i k => if k = j then (if i = 0 then u.1 else u.2) else X i k


def colFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 3)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) : ℂ :=
  letI := localBorel ℚ v
  ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
    Φ (setCol23 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))


def colFourier22 (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 2)
    (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  letI := localBorel ℚ v
  ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
    φ (setCol22 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))


def rowFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ :=
  colFourier23 v η 2 Φ


def matFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ :=
  colFourier23 v η 0 (colFourier23 v η 1 (colFourier23 v η 2 Φ))


def matFourier22 (η : AddChar (v.adicCompletion ℚ) ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ :=
  colFourier22 v η 0 (colFourier22 v η 1 φ)


def godementArg (h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.of fun i k =>
    Fin.lastCases ((transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i 1)
      (fun k' : Fin 2 => (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i k') k


def godementWhittaker3 (η : AddChar (v.adicCompletion ℚ) ℂ)
    (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (lam0 : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (g : LocalGL3 v) : ℂ :=
  letI := localGLBorel ℚ v
  ((lam0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
    * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
    * ∫ h : GL (Fin 2) (v.adicCompletion ℚ),
        rowFourier23 v η⁻¹
            (fun X => Φ (X * ((g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) h⁻¹)
            (godementArg v h)
          * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) ∂μ₂


def godementZeta2 (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (c : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  letI := localGLBorel ℚ v
  ∫ g : GL (Fin 2) (v.adicCompletion ℚ),
    c g * φ ((g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
      * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
      * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s ∂μ₂

end GodementSection

end LanglandsTunnell.CubicInduction

end
