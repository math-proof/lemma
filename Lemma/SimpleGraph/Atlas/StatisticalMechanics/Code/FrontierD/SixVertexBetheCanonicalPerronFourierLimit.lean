import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourierLimit
open Filter Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexRegularizedRapidityDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedRapidityDelta_eq
  {l : Filter ι}
  {epsilon : ι → Real}
  {lam : Real}
-- given
  (hepsilon : Tendsto epsilon l (nhds 0)) :
-- imply
  Tendsto (fun i => sixVertexRegularizedRapidityDelta lam (epsilon i)) l (nhds 1) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedRapidityDelta hepsilon

/--
[tendsto_sixVertexRegularizedRapidityRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedRapidityRadius_eq
  {l : Filter ι}
  {epsilon : ι → Real}
  {lam : Real}
-- given
  (hepsilon : Tendsto epsilon l (nhds 0))
  (hepsilonPos : ∀ᶠ i in l, 0 < epsilon i)
  (hlam : 0 < lam) :
-- imply
  Tendsto (fun i => sixVertexRegularizedRapidityRadius lam (epsilon i)) l (nhds 1) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedRapidityRadius hepsilon hepsilonPos hlam

/--
[tendsto_sixVertexRegularizedRapidityConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedRapidityConstant_eq
  {l : Filter ι}
  {epsilon : ι → Real}
  {lam : Real}
-- given
  (hepsilon : Tendsto epsilon l (nhds 0))
  (hepsilonPos : ∀ᶠ i in l, 0 < epsilon i)
  (hlam : 0 < lam) :
-- imply
  Tendsto (fun i => sixVertexRegularizedRapidityConstant lam (epsilon i)) l (nhds lam) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedRapidityConstant hepsilon hepsilonPos hlam

/--
[tendsto_sixVertexAbelRootDensitySeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexAbelRootDensitySeries_eq
  {l : Filter ι}
  {r : ι → Real}
  {lam : Real}
-- given
  (hlam : 0 < lam)
  (hr : Tendsto r l (nhds 1))
  (hrMem : ∀ᶠ i in l, r i ∈ Set.Icc 0 1) :
-- imply
  Tendsto (fun i => ∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam (r i) n) l (nhds (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexAbelRootDensitySeries hlam hr hrMem

/--
[summable_sixVertexAbelRootDensitySeriesTerm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma summable_sixVertexAbelRootDensitySeriesTerm_one_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (sixVertexAbelRootDensitySeriesTerm lam 1) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexAbelRootDensitySeriesTerm_one hlam

/--
[sixVertexAbelRootDensitySeriesTerm_one_sub_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma sixVertexAbelRootDensitySeriesTerm_one_sub_radius_eq_eq
  {lam : Real}
  {n : Nat} :
-- imply
  sixVertexAbelRootDensitySeriesTerm lam 1 n - sixVertexAbelRootDensitySeriesTerm lam (sixVertexFreeEnergyRapidityRadius lam) n = 2 * sixVertexFreeEnergySeriesTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexAbelRootDensitySeriesTerm_one_sub_radius_eq n

/--
[tendsto_sixVertexRegularizedRapidityFourierValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedRapidityFourierValue_eq
  {l : Filter ι}
  {epsilon : ι → Real}
  {lam : Real}
-- given
  (hepsilon : Tendsto epsilon l (nhds 0))
  (hepsilonPos : ∀ᶠ i in l, 0 < epsilon i)
  (hlam : 0 < lam) :
-- imply
  Tendsto (fun i => sixVertexRegularizedRapidityFourierValue lam (epsilon i)) l (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedRapidityFourierValue hepsilon hepsilonPos hlam

/--
[tendsto_sixVertexCanonicalPerronRegularizedIntegral_fourierValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRegularizedIntegral_fourierValue_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalPerronRegularizedIntegral hc) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRegularizedIntegral_fourierValue hc

/--
[tendsto_sixVertexCanonicalPerronRootAverage_fourierValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRootAverage_fourierValue_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRootAverage_fourierValue hc

/--
[tendsto_sixVertexCentralWidthRate_fourierValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourierLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCentralWidthRate_fourierValue_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCentralWidthRate c) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCentralWidthRate_fourierValue hc


-- created on 2026-10-23
