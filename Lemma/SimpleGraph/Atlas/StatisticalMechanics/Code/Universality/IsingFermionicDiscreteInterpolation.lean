import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation
open Filter Metric Set Topology StatMech StatMech.FrontierA StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[equicontinuousFamily_restrictionClosure_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean)
-/
@[path]
private lemma equicontinuousFamily_restrictionClosure_compact_eq
  {F : ι → Complex → Complex}
  {K : Set Complex}
-- given
  (hK : IsCompact K)
  (heq : EquicontinuousOn F K)
  (hbounded : ∃ C : Real, ∀ i z, z ∈ K → ‖F i z‖ ≤ C) :
-- imply
  IsCompact (closure (Set.range (fun i => UniformFun.ofFun (fun z : K => F i z)))) := by
-- proof
  apply StatMech.FrontierA.equicontinuousFamily_restrictionClosure_compact F K hK heq hbounded

/--
[equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean)
-/
@[path]
private lemma equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion_eq
  {F : Nat → Complex → Complex}
  {U : Set Complex}
  {E : CompactExhaustion U}
-- given
  (hU : IsOpen U)
  (heq : ∀ K : Set Complex, IsCompact K → K ⊆ U → EquicontinuousOn F K)
  (hbounded : ∀ K : Set Complex, IsCompact K → K ⊆ U → ∃ C : Real, ∀ n z, z ∈ K → ‖F n z‖ ≤ C) :
-- imply
  IsLocallyUniformlySequentiallyPrecompact F U := by
-- proof
  apply StatMech.FrontierA.equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion F U hU heq hbounded E

/--
[stableInterpolant_compact_eventually_near_literalObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean)
-/
@[path]
private lemma stableInterpolant_compact_eventually_near_literalObservable_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.StableDiscreteInterpolation}
  {K : Set Complex}
-- given
  (hK : IsCompact K)
  (hKU : K ⊆ A.U) :
-- imply
  ∀ᶠ n in atTop, ∀ z ∈ K, ∃ e : A.M n, dist z (A.medialEmbedding n e) ≤ A.mesh n ∧ I.interpolant n (A.medialEmbedding n e) = @FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.stableInterpolant_compact_eventually_near_literalObservable A I K hK hKU

/--
[StableDiscreteInterpolation.locallyUniformlySequentiallyPrecompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean)
-/
@[path]
private lemma locallyUniformlySequentiallyPrecompact_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.StableDiscreteInterpolation}
  {E : StatMech.FrontierA.CompactExhaustion A.U}
-- given
  (hbounded : I.HasCompactLocalBounds) :
-- imply
  StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact I.interpolant A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableDiscreteInterpolation.locallyUniformlySequentiallyPrecompact A I E hbounded

/--
[StableDiscreteInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean)
-/
@[path]
private lemma scalingLimit_of_compactBounds_and_moreraPrimitive_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.StableDiscreteInterpolation}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion A.U}
-- given
  (htarget : DifferentiableOn Complex target A.U)
  (htarget_ne : target A.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi A.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
  (hbounded : I.HasCompactLocalBounds)
  (hidentify : StableDiscreteInterpolation.SubsequentialMoreraPrimitive A I target Phi) :
-- imply
  TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableDiscreteInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive A I target Phi htarget htarget_ne hPhi hPhideriv E hbounded hidentify

/--
[StableDiscreteInterpolation.literalObservable_tendsto_on_compacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean)
-/
@[path]
private lemma literalObservable_tendsto_on_compacts_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.StableDiscreteInterpolation}
  {target : Complex → Complex}
  {K : Set Complex}
  {epsilon : Real}
-- given
  (hlimit : TendstoLocallyUniformlyOn I.interpolant target atTop A.U)
  (hK : IsCompact K)
  (hKU : K ⊆ A.U)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ n in atTop, ∀ e : A.M n, A.medialEmbedding n e ∈ K → dist (@FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e) (target (A.medialEmbedding n e)) < epsilon := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableDiscreteInterpolation.literalObservable_tendsto_on_compacts A I target hlimit K hK hKU epsilon hepsilon


-- created on 2026-10-23
