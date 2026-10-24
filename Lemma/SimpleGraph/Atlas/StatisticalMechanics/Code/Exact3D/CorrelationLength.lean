import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.CorrelationLength
open StatMech StatMech.Exact3D


/--
[logSlope_congr_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma logSlope_congr_betaC_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
  {β : ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  logSlope M correlationLength β = logSlope N correlationLength β := by
-- proof
  apply StatMech.Exact3D.logSlope_congr_betaC hβc correlationLength β

/--
[HasCriticalNu.congr_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma congr_betaC_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hν : HasCriticalNu M correlationLength ν)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu N correlationLength ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.congr_betaC hν hβc

/--
[HasCriticalNu.congr_betaC_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma congr_betaC_iff_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength ν ↔ HasCriticalNu N correlationLength ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.congr_betaC_iff hβc

/--
[HasCriticalNu.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma congr_eventually_eq
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hν : HasCriticalNu M correlationLength ν)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.congr_eventually hν hEq

/--
[HasCriticalNu.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma congr_eventually_iff_eq
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength β) :
-- imply
  HasCriticalNu M correlationLength ν ↔ HasCriticalNu M comparisonLength ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.congr_eventually_iff hEq

/--
[HasCorrelationLength.positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma positive_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
-- given
  (hξ : HasCorrelationLength M β origin ray ξ) :
-- imply
  0 < ξ := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.positive hξ

/--
[HasInverseCorrelationLength.unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma unique_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m₁ m₂ : ℝ}
-- given
  (h₁ : HasInverseCorrelationLength M β origin ray m₁)
  (h₂ : HasInverseCorrelationLength M β origin ray m₂) :
-- imply
  m₁ = m₂ := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.unique h₁ h₂

/--
[HasInverseCorrelationLength.lowerInverseCorrelationLength_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma lowerInverseCorrelationLength_eq_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m : ℝ}
-- given
  (h : HasInverseCorrelationLength M β origin ray m) :
-- imply
  lowerInverseCorrelationLength M β origin ray = m := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.lowerInverseCorrelationLength_eq h

/--
[HasInverseCorrelationLength.upperInverseCorrelationLength_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma upperInverseCorrelationLength_eq_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m : ℝ}
-- given
  (h : HasInverseCorrelationLength M β origin ray m) :
-- imply
  upperInverseCorrelationLength M β origin ray = m := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.upperInverseCorrelationLength_eq h

/--
[HasInverseCorrelationLength.lower_eq_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma lower_eq_upper_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m : ℝ}
-- given
  (h : HasInverseCorrelationLength M β origin ray m) :
-- imply
  lowerInverseCorrelationLength M β origin ray = upperInverseCorrelationLength M β origin ray := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.lower_eq_upper h

/--
[inverseDecayRate_congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma inverseDecayRate_congr_eventually_eq
  {M N : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  ∀ᶠ n in Filter.atTop, inverseDecayRate M β origin ray n = inverseDecayRate N β origin ray n := by
-- proof
  apply StatMech.Exact3D.inverseDecayRate_congr_eventually hEq

/--
[lowerInverseCorrelationLength_congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma lowerInverseCorrelationLength_congr_eventually_eq
  {M N : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  lowerInverseCorrelationLength M β origin ray = lowerInverseCorrelationLength N β origin ray := by
-- proof
  apply StatMech.Exact3D.lowerInverseCorrelationLength_congr_eventually hEq

/--
[upperInverseCorrelationLength_congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma upperInverseCorrelationLength_congr_eventually_eq
  {M N : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  upperInverseCorrelationLength M β origin ray = upperInverseCorrelationLength N β origin ray := by
-- proof
  apply StatMech.Exact3D.upperInverseCorrelationLength_congr_eventually hEq

/--
[liminfCorrelationLength_congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma liminfCorrelationLength_congr_eventually_eq
  {M N : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  liminfCorrelationLength M β origin ray = liminfCorrelationLength N β origin ray := by
-- proof
  apply StatMech.Exact3D.liminfCorrelationLength_congr_eventually hEq

/--
[HasCriticalNu.liminfCorrelationLength_congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma liminfCorrelationLength_congr_eventually_iff_eq
  {M N : CriticalModel ι}
  {origin : ι}
  {ray : ℕ → ι}
  {ν : ℝ}
-- given
  (hβc : M.betaC = N.betaC)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  HasCriticalNu M (fun β => liminfCorrelationLength M β origin ray) ν ↔ HasCriticalNu N (fun β => liminfCorrelationLength N β origin ray) ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.liminfCorrelationLength_congr_eventually_iff hβc hEq

/--
[HasInverseCorrelationLength.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma congr_eventually_eq_2
  {M N : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m : ℝ}
-- given
  (h : HasInverseCorrelationLength M β origin ray m)
  (hEq : ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  HasInverseCorrelationLength N β origin ray m := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.congr_eventually h hEq

/--
[HasInverseCorrelationLength.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma congr_eventually_iff_eq_2
  {M N : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m : ℝ}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  HasInverseCorrelationLength M β origin ray m ↔ HasInverseCorrelationLength N β origin ray m := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.congr_eventually_iff hEq

/--
[HasInverseCorrelationLength.hasCorrelationLength_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma hasCorrelationLength_inv_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m : ℝ}
-- given
  (h : HasInverseCorrelationLength M β origin ray m)
  (hm : 0 < m) :
-- imply
  HasCorrelationLength M β origin ray m⁻¹ where xi_pos := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.hasCorrelationLength_inv h hm

/--
[HasCorrelationLength.unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma unique_eq_2
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ₁ ξ₂ : ℝ}
-- given
  (h₁ : HasCorrelationLength M β origin ray ξ₁)
  (h₂ : HasCorrelationLength M β origin ray ξ₂) :
-- imply
  ξ₁ = ξ₂ := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.unique h₁ h₂

/--
[HasCorrelationLength.lowerInverseCorrelationLength_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma lowerInverseCorrelationLength_eq_eq_2
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
-- given
  (h : HasCorrelationLength M β origin ray ξ) :
-- imply
  lowerInverseCorrelationLength M β origin ray = ξ⁻¹ := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.lowerInverseCorrelationLength_eq h

/--
[HasCorrelationLength.upperInverseCorrelationLength_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma upperInverseCorrelationLength_eq_eq_2
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
-- given
  (h : HasCorrelationLength M β origin ray ξ) :
-- imply
  upperInverseCorrelationLength M β origin ray = ξ⁻¹ := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.upperInverseCorrelationLength_eq h

/--
[HasCorrelationLength.lower_eq_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma lower_eq_upper_eq_2
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
-- given
  (h : HasCorrelationLength M β origin ray ξ) :
-- imply
  lowerInverseCorrelationLength M β origin ray = upperInverseCorrelationLength M β origin ray := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.lower_eq_upper h

/--
[HasCorrelationLength.liminfCorrelationLength_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma liminfCorrelationLength_eq_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
-- given
  (h : HasCorrelationLength M β origin ray ξ) :
-- imply
  liminfCorrelationLength M β origin ray = ξ := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.liminfCorrelationLength_eq h

/--
[HasCorrelationLength.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma congr_eventually_eq_3
  {M N : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
-- given
  (h : HasCorrelationLength M β origin ray ξ)
  (hEq : ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  HasCorrelationLength N β origin ray ξ where xi_pos := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.congr_eventually h hEq

/--
[HasCorrelationLength.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma congr_eventually_iff_eq_3
  {M N : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, TwoPointAlongRay M β origin ray n = TwoPointAlongRay N β origin ray n) :
-- imply
  HasCorrelationLength M β origin ray ξ ↔ HasCorrelationLength N β origin ray ξ := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.congr_eventually_iff hEq

/--
[finiteDistanceDecayRate_rescale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma finiteDistanceDecayRate_rescale_eq
  {G : ℕ → ℝ}
  {L n : ℕ}
-- given
  (hL : L ≠ 0)
  (hn : n ≠ 0) :
-- imply
  finiteDistanceDecayRate (fun k => G (L * k)) n = (L : ℝ) * finiteDistanceDecayRate G (L * n) := by
-- proof
  apply StatMech.Exact3D.finiteDistanceDecayRate_rescale G hL hn

/--
[tendsto_nat_mul_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma tendsto_nat_mul_atTop_eq
  {L : ℕ}
-- given
  (hL : L ≠ 0) :
-- imply
  Filter.Tendsto (fun n : ℕ => L * n) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Exact3D.tendsto_nat_mul_atTop hL

/--
[HasInverseCorrelationLength.rescale_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma rescale_nat_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m : ℝ}
  {L : ℕ}
-- given
  (hL : L ≠ 0)
  (h : HasInverseCorrelationLength M β origin ray m) :
-- imply
  HasInverseCorrelationLength M β origin (fun n => ray (L * n)) ((L : ℝ) * m) := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.rescale_nat hL h

/--
[HasCorrelationLength.rescale_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean)
-/
@[path]
private lemma rescale_nat_eq_2
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
  {L : ℕ}
-- given
  (hL : L ≠ 0)
  (h : HasCorrelationLength M β origin ray ξ) :
-- imply
  HasCorrelationLength M β origin (fun n => ray (L * n)) (ξ / (L : ℝ)) where xi_pos := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.rescale_nat hL h


-- created on 2026-10-23
