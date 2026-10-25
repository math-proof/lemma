import Structure.AutomorphicForm_CuspidalSpectrumCarrier

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm.CuspidalConstituent


noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

variable (F : Type) [Field F] [NumberField F]

def IsCuspLift {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop :=
  ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ),
    S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩


structure IsClosedCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop where
  isClosed : IsClosed (M : Set ↥(cuspSubcarrier F hΦ₀ σ ξ))
  map_le_of_rightTranslate_fin : ∀ g ∈ finiteAdelicGL2Subgroup F,
    ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S →
        M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M
  map_le_of_rightTranslate_arch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
    ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S →
        M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M
  map_le_of_rightConv : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
    IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) S →
          M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M


end CuspidalSpectrum

end AutomorphicForm

end
