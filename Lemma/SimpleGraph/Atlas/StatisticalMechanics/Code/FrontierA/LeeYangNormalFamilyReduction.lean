import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangNormalFamilyReduction
open Filter Set Topology StatMech StatMech.FrontierA


/--
[tendstoLocallyUniformlyOn_of_subsequential_limits_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangNormalFamilyReduction.lean)
-/
@[path]
private lemma tendstoLocallyUniformlyOn_of_subsequential_limits_unique_eq
  {F : ℕ → ℂ → ℂ}
  {g : ℂ → ℂ}
  {U : Set ℂ}
-- given
  (hU : IsOpen U)
  (hcompact : IsLocallyUniformlySequentiallyPrecompact F U)
  (hunique : ∀ (φ ψ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ → StrictMono ψ → TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop U → Set.EqOn f g U) :
-- imply
  TendstoLocallyUniformlyOn F g atTop U := by
-- proof
  apply StatMech.FrontierA.tendstoLocallyUniformlyOn_of_subsequential_limits_unique F g U hU hcompact hunique

/--
[holomorphic_subsequentialLimits_unique_of_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangNormalFamilyReduction.lean)
-/
@[path]
private lemma holomorphic_subsequentialLimits_unique_of_anchor_eq
  {F : ℕ → ℂ → ℂ}
  {U anchor : Set ℂ}
  {z₀ : ℂ}
  {anchorLimit : ℂ → ℂ}
  {φ₁ ψ₁ φ₂ ψ₂ : ℕ → ℕ}
  {f g : ℂ → ℂ}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hanchorU : anchor ⊆ U)
  (hanchorAccum : ∃ᶠ z in nhdsWithin z₀ ({z₀}ᶜ), z ∈ anchor)
  (hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U)
  (hanchorLimit : ∀ z ∈ anchor, Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)))
  (hφ₁ : StrictMono φ₁)
  (hψ₁ : StrictMono ψ₁)
  (hφ₂ : StrictMono φ₂)
  (hψ₂ : StrictMono ψ₂)
  (hf : TendstoLocallyUniformlyOn (fun n => F (φ₁ (ψ₁ n))) f atTop U)
  (hg : TendstoLocallyUniformlyOn (fun n => F (φ₂ (ψ₂ n))) g atTop U) :
-- imply
  Set.EqOn f g U := by
-- proof
  apply StatMech.FrontierA.holomorphic_subsequentialLimits_unique_of_anchor F U anchor z₀ anchorLimit hUopen hUconnected hz₀ hanchorU hanchorAccum hholomorphic hanchorLimit φ₁ ψ₁ φ₂ ψ₂ f g hφ₁ hψ₁ hφ₂ hψ₂ hf hg

/--
[montelVitali_of_locallyUniform_precompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangNormalFamilyReduction.lean)
-/
@[path]
private lemma montelVitali_of_locallyUniform_precompact_eq
  {F : ℕ → ℂ → ℂ}
  {U anchor : Set ℂ}
  {z₀ : ℂ}
  {anchorLimit : ℂ → ℂ}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hanchorU : anchor ⊆ U)
  (hanchorAccum : ∃ᶠ z in nhdsWithin z₀ ({z₀}ᶜ), z ∈ anchor)
  (hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U)
  (hcompact : IsLocallyUniformlySequentiallyPrecompact F U)
  (hanchorLimit : ∀ z ∈ anchor, Tendsto (fun n => F n z) atTop (nhds (anchorLimit z))) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn F g atTop U ∧ DifferentiableOn ℂ g U ∧ TendstoLocallyUniformlyOn (deriv ∘ F) (deriv g) atTop U := by
-- proof
  apply StatMech.FrontierA.montelVitali_of_locallyUniform_precompact F U anchor z₀ anchorLimit hUopen hUconnected hz₀ hanchorU hanchorAccum hholomorphic hcompact hanchorLimit


-- created on 2026-10-23
