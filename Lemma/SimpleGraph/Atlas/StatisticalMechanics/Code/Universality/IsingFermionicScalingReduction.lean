import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicScalingReduction
open Filter Set Topology StatMech StatMech.Universality


/--
[isingFermionicNormalizedInterpolant_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicScalingReduction.lean)
-/
@[path]
private lemma isingFermionicNormalizedInterpolant_apply_eq
  {delta : Nat → Real}
  {raw : Nat → ℂ → ℂ}
  {n : Nat}
  {z : ℂ} :
-- imply
  isingFermionicNormalizedInterpolant delta raw n z = raw n z / (Real.sqrt (2 * delta n) : ℂ) := by
-- proof
  apply StatMech.Universality.isingFermionicNormalizedInterpolant_apply delta raw n z

/--
[isingFermionic_scalingLimit_of_compactBounds_and_primitiveIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicScalingReduction.lean)
-/
@[path]
private lemma isingFermionic_scalingLimit_of_compactBounds_and_primitiveIm_eq
  {delta : Nat → Real}
  {raw : Nat → ℂ → ℂ}
  {target Phi : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  {E : StatMech.FrontierA.CompactExhaustion U}
-- given
  (hUopen : IsOpen U)
  (hUconnected : IsPreconnected U)
  (hz₀ : z₀ ∈ U)
  (hF : ∀ n, DifferentiableOn ℂ (isingFermionicNormalizedInterpolant delta raw n) U)
  (htarget : DifferentiableOn ℂ target U)
  (htarget_ne : target z₀ ≠ 0)
  (hPhi : DifferentiableOn ℂ Phi U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) U)
  (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ C : Real, ∀ n z, z ∈ K → ‖isingFermionicNormalizedInterpolant delta raw n z‖ ≤ C)
  (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : ℂ → ℂ), StrictMono phi → StrictMono psi → TendstoLocallyUniformlyOn (fun n ↦ isingFermionicNormalizedInterpolant delta raw (phi (psi n))) f atTop U → ∃ (P : ℂ → ℂ) (C : Real), DifferentiableOn ℂ P U ∧ Set.EqOn (deriv P) (fun z ↦ f z ^ 2) U ∧ (∀ z ∈ U, (P z).im = (Phi z).im + C) ∧ f z₀ = target z₀) :
-- imply
  TendstoLocallyUniformlyOn (isingFermionicNormalizedInterpolant delta raw) target atTop U ∧ TendstoLocallyUniformlyOn (deriv ∘ isingFermionicNormalizedInterpolant delta raw) (deriv target) atTop U := by
-- proof
  apply StatMech.Universality.isingFermionic_scalingLimit_of_compactBounds_and_primitiveIm delta raw target Phi U z₀ hUopen hUconnected hz₀ hF htarget htarget_ne hPhi hPhideriv E hbounded hidentifyPrimitive


-- created on 2026-10-23
