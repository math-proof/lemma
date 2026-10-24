import Lemma.Definitions.Def_AutomorphicForm_UnipotentQuotient
import Lemma.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Lemma.Definitions.Def_NumberField_TateGlobalZeta
import Lemma.Definitions.Def_AutomorphicForm_WeylIntertwining

open MeasureTheory NumberField AutomorphicForm Matrix

noncomputable section

namespace RSCarrier

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

def rsLocalIntegral (μ : Measure G) (H : Subgroup G) (μH : Measure H) (δ : G → ℝ) (s : ℂ)
    (W F : G → ℂ) : ℂ :=
  ∫ g, (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2) ∂(μ.withDensity (HaarQuotient.density H μH))

end Generic

section Arch

abbrev realUnipotent : Subgroup (GL (Fin 2) ℝ) :=
  (unipotentGL2Hom (R := ℝ)).range

def rsArchIntegral [MeasurableSpace (GL (Fin 2) ℝ)] (μ : Measure (GL (Fin 2) ℝ))
    (μN : Measure realUnipotent) (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ) : ℂ :=
  rsLocalIntegral μ realUnipotent μN (fun g => |(GeneralLinearGroup.det g : ℝ)|) s W F

def transposeInv (g : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  ⟨((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ, (g : Matrix (Fin 2) (Fin 2) ℝ)ᵀ,
    by rw [← Matrix.transpose_mul]; simp,
    by rw [← Matrix.transpose_mul]; simp⟩

def archDual (W : GL (Fin 2) ℝ → ℂ) : GL (Fin 2) ℝ → ℂ :=
  fun g => W ((AutomorphicForm.gl2Weyl : GL (Fin 2) ℝ) * transposeInv g)

end Arch

section Finite

abbrev finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ) :=
  (adelicUnipotent ℚ).subgroupOf (finiteAdelicGL2Subgroup ℚ)

def rsFinIntegral [MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ)] (μ : Measure (finiteAdelicGL2Subgroup ℚ))
    (μN : Measure finUnipotent) (s : ℂ) (W F : finiteAdelicGL2Subgroup ℚ → ℂ) : ℂ :=
  rsLocalIntegral μ finUnipotent μN
    (fun g => TateGlobal.ideleNorm ℚ (GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ))) s W F

end Finite

end RSCarrier

end
