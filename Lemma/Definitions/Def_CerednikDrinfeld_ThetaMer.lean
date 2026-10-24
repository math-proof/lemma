import Lemma.Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open Classical CerednikDrinfeld.Omega

namespace CerednikDrinfeld.Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

def IsThetaPair (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (F H : ↥(holRing ϖ)) : Prop :=
  H ∈ nonZeroDivisors ↥(holRing ϖ) ∧
  (∀ z : ↥(upperHalfPlane K₀ K),
    (H : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)) ∧
  (∀ z : ↥(upperHalfPlane K₀ K),
    (F : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) ∧
  (∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)) →
    (F : ↥(upperHalfPlane K₀ K) → K) z / (H : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a b z₀ (z : K))

def thetaMer (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K) : merField ϖ :=
  if h : ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H then
    Localization.mk h.choose ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩
  else 0

theorem thetaMer_def_of_exists (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (h : ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ = Localization.mk h.choose ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩ :=
  dif_pos h

theorem thetaMer_of_not_exists (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (h : ¬ ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H) : thetaMer ϖ ρ a b z₀ = 0 :=
  dif_neg h

end CerednikDrinfeld.Omega

end
