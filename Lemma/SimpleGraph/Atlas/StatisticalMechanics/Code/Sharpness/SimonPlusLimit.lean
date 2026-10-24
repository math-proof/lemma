import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.SimonPlusLimit
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech StatMech.Sharpness


/--
[spinPairBCF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean)
-/
@[path]
private lemma spinPairBCF_apply_eq
  {d : ℕ}
  {x y : Site d}
  {ω : ConfigSpace (Site d)} :
-- imply
  spinPairBCF x y ω = spin ω x * spin ω y := by
-- proof
  apply StatMech.Sharpness.spinPairBCF_apply x y ω

/--
[plusMeasure_pair_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean)
-/
@[path]
private lemma plusMeasure_pair_tendsto_eq
  {d : ℕ}
  {β : ℝ}
  {φ : ℕ → ℕ}
  {x y : Site d}
-- given
  (hconv : WeakConvergesTo (fun n ↦ plusMeasure d (φ n) β 0) (plusState d β 0)) :
-- imply
  Tendsto (fun n ↦ ∫ ω, spin ω x * spin ω y ∂(plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (plusCorr d β x y)) := by
-- proof
  apply StatMech.Sharpness.plusMeasure_pair_tendsto β φ hconv x y

/--
[simonBoundaryIntegral_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean)
-/
@[path]
private lemma simonBoundaryIntegral_tendsto_eq
  {d : ℕ}
  {β : ℝ}
  {φ : ℕ → ℕ}
  {S : Finset (Site d)}
  {o z : Site d}
-- given
  (hconv : WeakConvergesTo (fun n ↦ plusMeasure d (φ n) β 0) (plusState d β 0)) :
-- imply
  Tendsto (fun n ↦ simonBoundaryIntegral β S o z (plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (simonBoundaryPlus β S o z)) := by
-- proof
  apply StatMech.Sharpness.simonBoundaryIntegral_tendsto β φ hconv S o z

/--
[plusCorr_simon_of_eventually_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean)
-/
@[path]
private lemma plusCorr_simon_of_eventually_finite_eq
  {d : ℕ}
  {β : ℝ}
  {S : Finset (Site d)}
  {o z : Site d}
-- given
  (hfinite : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ᶠ n in atTop, (∫ ω, spin ω o * spin ω z ∂(plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d)))) ≤ simonBoundaryIntegral β S o z (plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d)))) :
-- imply
  plusCorr d β o z ≤ simonBoundaryPlus β S o z := by
-- proof
  apply StatMech.Sharpness.plusCorr_simon_of_eventually_finite β S o z hfinite


-- created on 2026-10-23
