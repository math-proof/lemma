import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Lemma.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Lemma.Definitions.Def_AutomorphicForm_SmoothingKernel
import Lemma.Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal

namespace LanglandsTunnell.CubicInduction

section GodementSection

variable (v : HeightOneSpectrum (𝓞 ℚ))

def setCol23 (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (j : Fin 3)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.of fun i k => if k = j then (if i = 0 then u.1 else u.2) else X i k

theorem setCol23_apply (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (j : Fin 3)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) (i : Fin 2) (k : Fin 3) :
    setCol23 v X j u i k = if k = j then (if i = 0 then u.1 else u.2) else X i k :=
  rfl

def setCol22 (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (j : Fin 2)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  Matrix.of fun i k => if k = j then (if i = 0 then u.1 else u.2) else X i k

theorem setCol22_apply (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (j : Fin 2)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) (i k : Fin 2) :
    setCol22 v X j u i k = if k = j then (if i = 0 then u.1 else u.2) else X i k :=
  rfl

def colFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 3)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) : ℂ :=
  letI := localBorel ℚ v
  ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
    Φ (setCol23 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))

theorem colFourier23_apply (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 3)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    colFourier23 v η j Φ X =
      letI := localBorel ℚ v
      ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
        Φ (setCol23 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
  rfl

def colFourier22 (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 2)
    (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  letI := localBorel ℚ v
  ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
    φ (setCol22 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))

theorem colFourier22_apply (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 2)
    (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    colFourier22 v η j φ X =
      letI := localBorel ℚ v
      ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
        φ (setCol22 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
  rfl

def rowFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ :=
  colFourier23 v η 2 Φ

theorem rowFourier23_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    rowFourier23 v η Φ = colFourier23 v η 2 Φ :=
  rfl

def matFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ :=
  colFourier23 v η 0 (colFourier23 v η 1 (colFourier23 v η 2 Φ))

theorem matFourier23_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    matFourier23 v η Φ = colFourier23 v η 0 (colFourier23 v η 1 (colFourier23 v η 2 Φ)) :=
  rfl

def matFourier22 (η : AddChar (v.adicCompletion ℚ) ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ :=
  colFourier22 v η 0 (colFourier22 v η 1 φ)

theorem matFourier22_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    matFourier22 v η φ = colFourier22 v η 0 (colFourier22 v η 1 φ) :=
  rfl

def godementArg (h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.of fun i k =>
    Fin.lastCases ((transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i 1)
      (fun k' : Fin 2 => (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i k') k

theorem godementArg_apply_castSucc (h : GL (Fin 2) (v.adicCompletion ℚ)) (i k : Fin 2) :
    godementArg v h i (Fin.castSucc k) = (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i k := by
  simp only [godementArg, Matrix.of_apply, Fin.lastCases_castSucc]

theorem godementArg_apply_last (h : GL (Fin 2) (v.adicCompletion ℚ)) (i : Fin 2) :
    godementArg v h i (Fin.last 2) = (transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i 1 := by
  simp only [godementArg, Matrix.of_apply, Fin.lastCases_last]

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

theorem godementWhittaker3_apply (η : AddChar (v.adicCompletion ℚ) ℂ)
    (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (lam0 : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (g : LocalGL3 v) :
    godementWhittaker3 v η μ₂ lam0 Φ g =
      letI := localGLBorel ℚ v
      ((lam0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
        * ∫ h : GL (Fin 2) (v.adicCompletion ℚ),
            rowFourier23 v η⁻¹
                (fun X => Φ (X * ((g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) h⁻¹)
                (godementArg v h)
              * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
              * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
                  ^ (1 / 2 : ℂ) ∂μ₂ :=
  rfl

def godementZeta2 (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (c : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  letI := localGLBorel ℚ v
  ∫ g : GL (Fin 2) (v.adicCompletion ℚ),
    c g * φ ((g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
      * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
      * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s ∂μ₂

theorem godementZeta2_apply (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (c : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    godementZeta2 v μ₂ c φ χ s =
      letI := localGLBorel ℚ v
      ∫ g : GL (Fin 2) (v.adicCompletion ℚ),
        c g * φ ((g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
          * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s ∂μ₂ :=
  rfl

end GodementSection

end LanglandsTunnell.CubicInduction

end
