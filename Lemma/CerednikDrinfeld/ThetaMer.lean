import Lemma.CerednikDrinfeld.DrinfeldHolomorphic
import Def.CerednikDrinfeld_ThetaMer

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open Classical CerednikDrinfeld.Omega

namespace CerednikDrinfeld.Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]


theorem thetaMer_def_of_exists (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (h : ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ = Localization.mk h.choose ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩ :=
  dif_pos h

theorem thetaMer_of_not_exists (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (h : ¬ ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H) : thetaMer ϖ ρ a b z₀ = 0 :=
  dif_neg h

end CerednikDrinfeld.Omega

end
