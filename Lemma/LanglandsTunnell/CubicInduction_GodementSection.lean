import Lemma.LanglandsTunnell.CubicInduction_PrincipalSeries3
import Lemma.LanglandsTunnell.StandardLocalConstantsAt
import Lemma.AutomorphicForm.SmoothingKernel
import Lemma.AutomorphicForm.LocalOrbitalBase
import Def.LanglandsTunnell_CubicInduction_GodementSection

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal

namespace LanglandsTunnell.CubicInduction

section GodementSection

variable (v : HeightOneSpectrum (𝓞 ℚ))


theorem setCol23_apply (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (j : Fin 3)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) (i : Fin 2) (k : Fin 3) :
    setCol23 v X j u i k = if k = j then (if i = 0 then u.1 else u.2) else X i k :=
  rfl


theorem setCol22_apply (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (j : Fin 2)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) (i k : Fin 2) :
    setCol22 v X j u i k = if k = j then (if i = 0 then u.1 else u.2) else X i k :=
  rfl


theorem colFourier23_apply (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 3)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    colFourier23 v η j Φ X =
      letI := localBorel ℚ v
      ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
        Φ (setCol23 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
  rfl


theorem colFourier22_apply (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 2)
    (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    colFourier22 v η j φ X =
      letI := localBorel ℚ v
      ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
        φ (setCol22 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
  rfl


theorem rowFourier23_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    rowFourier23 v η Φ = colFourier23 v η 2 Φ :=
  rfl


theorem matFourier23_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    matFourier23 v η Φ = colFourier23 v η 0 (colFourier23 v η 1 (colFourier23 v η 2 Φ)) :=
  rfl


theorem matFourier22_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    matFourier22 v η φ = colFourier22 v η 0 (colFourier22 v η 1 φ) :=
  rfl


theorem godementArg_apply_castSucc (h : GL (Fin 2) (v.adicCompletion ℚ)) (i k : Fin 2) :
    godementArg v h i (Fin.castSucc k) = (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i k := by
  simp only [godementArg, Matrix.of_apply, Fin.lastCases_castSucc]

theorem godementArg_apply_last (h : GL (Fin 2) (v.adicCompletion ℚ)) (i : Fin 2) :
    godementArg v h i (Fin.last 2) = (transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i 1 := by
  simp only [godementArg, Matrix.of_apply, Fin.lastCases_last]


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
