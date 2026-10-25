import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformArcosh
open Filter Set StatMech StatMech.FrontierA


/--
[eventually_one_le_quantumIsingTrotterReducedParameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformArcosh.lean)
-/
@[path]
private lemma eventually_one_le_quantumIsingTrotterReducedParameter_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  ∀ᶠ n : Nat in atTop, ∀ k : Real, 1 <= quantumIsingTrotterReducedParameter beta h (n + 1) k := by
-- proof
  apply StatMech.FrontierA.eventually_one_le_quantumIsingTrotterReducedParameter beta h hbeta hh

/--
[quantumIsingTrotterReducedParameter_tendstoUniformly_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformArcosh.lean)
-/
@[path]
private lemma quantumIsingTrotterReducedParameter_tendstoUniformly_one_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta) :
-- imply
  TendstoUniformly (fun n k => quantumIsingTrotterReducedParameter beta h (n + 1) k) (fun _ => 1) atTop := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterReducedParameter_tendstoUniformly_one beta h hbeta

/--
[quantumIsingTrotter_arcosh_tendstoUniformly_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformArcosh.lean)
-/
@[path]
private lemma quantumIsingTrotter_arcosh_tendstoUniformly_zero_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  TendstoUniformly (fun n k => Real.arcosh (quantumIsingTrotterReducedParameter beta h (n + 1) k)) (fun _ => 0) atTop := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotter_arcosh_tendstoUniformly_zero beta h hbeta hh

/--
[quantumIsing_arcoshQuadraticRatio_tendstoUniformly_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformArcosh.lean)
-/
@[path]
private lemma quantumIsing_arcoshQuadraticRatio_tendstoUniformly_two_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  TendstoUniformly (fun n k => arcoshQuadraticRatio (Real.arcosh (quantumIsingTrotterReducedParameter beta h (n + 1) k))) (fun _ => 2) atTop := by
-- proof
  apply StatMech.FrontierA.quantumIsing_arcoshQuadraticRatio_tendstoUniformly_two beta h hbeta hh

/--
[quantumIsingScaledArcosh_tendstoUniformly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformArcosh.lean)
-/
@[path]
private lemma quantumIsingScaledArcosh_tendstoUniformly_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  TendstoUniformly (fun n k => quantumIsingScaledArcosh beta h n k) (fun k => Real.sqrt (2 * quantumIsingScaledReducedLimit beta h k)) atTop := by
-- proof
  apply StatMech.FrontierA.quantumIsingScaledArcosh_tendstoUniformly beta h hbeta hh

/--
[sqrt_two_mul_quantumIsingScaledReducedLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformArcosh.lean)
-/
@[path]
private lemma sqrt_two_mul_quantumIsingScaledReducedLimit_eq
-- given
  (beta h k : Real)
  (hbeta : 0 < beta) :
-- imply
  Real.sqrt (2 * quantumIsingScaledReducedLimit beta h k) = beta / 2 * quantumIsingDispersion h k := by
-- proof
  apply StatMech.FrontierA.sqrt_two_mul_quantumIsingScaledReducedLimit beta h k hbeta

/--
[quantumIsingScaledArcosh_tendstoUniformly_dispersion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformArcosh.lean)
-/
@[path]
private lemma quantumIsingScaledArcosh_tendstoUniformly_dispersion_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  TendstoUniformly (fun n k => quantumIsingScaledArcosh beta h n k) (fun k => beta / 2 * quantumIsingDispersion h k) atTop := by
-- proof
  apply StatMech.FrontierA.quantumIsingScaledArcosh_tendstoUniformly_dispersion beta h hbeta hh


-- created on 2026-10-23
