import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingArcoshAsymptotic
open Filter Set Topology StatMech StatMech.FrontierA


/--
[arcoshQuadraticRatio_tendsto_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArcoshAsymptotic.lean)
-/
@[path]
private lemma arcoshQuadraticRatio_tendsto_two_eq :
-- imply
  Tendsto arcoshQuadraticRatio (nhdsWithin 0 (Ici 0)) (nhds 2) := by
-- proof
  apply StatMech.FrontierA.arcoshQuadraticRatio_tendsto_two

/--
[continuousOn_arcoshQuadraticRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArcoshAsymptotic.lean)
-/
@[path]
private lemma continuousOn_arcoshQuadraticRatio_eq :
-- imply
  ContinuousOn arcoshQuadraticRatio (Ici 0) := by
-- proof
  apply StatMech.FrontierA.continuousOn_arcoshQuadraticRatio

/--
[arcoshQuadraticRatio_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArcoshAsymptotic.lean)
-/
@[path]
private lemma arcoshQuadraticRatio_pos_eq
  {u : Real}
-- given
  (hu : 0 <= u) :
-- imply
  0 < arcoshQuadraticRatio u := by
-- proof
  apply StatMech.FrontierA.arcoshQuadraticRatio_pos hu

/--
[scaled_arcosh_sq_eq_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArcoshAsymptotic.lean)
-/
@[path]
private lemma scaled_arcosh_sq_eq_ratio_eq
  {scale A : Real}
-- given
  (hA : 1 <= A) :
-- imply
  (scale * Real.arcosh A) ^ 2 = arcoshQuadraticRatio (Real.arcosh A) * (scale ^ 2 * (A - 1)) := by
-- proof
  apply StatMech.FrontierA.scaled_arcosh_sq_eq_ratio scale A hA

/--
[arcosh_scaled_tendsto_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArcoshAsymptotic.lean)
-/
@[path]
private lemma arcosh_scaled_tendsto_sqrt_eq
  {c : Real}
-- given
  (A : Nat -> Real)
  (hscaled : Tendsto (fun n : Nat => (n + 1 : Real) ^ 2 * (A n - 1)) atTop (nhds c))
  (hbranch : ∀ᶠ n in atTop, 1 <= A n) :
-- imply
  Tendsto (fun n : Nat => (n + 1 : Real) * Real.arcosh (A n)) atTop (nhds (Real.sqrt (2 * c))) := by
-- proof
  apply StatMech.FrontierA.arcosh_scaled_tendsto_sqrt A hscaled hbranch


-- created on 2026-10-23
