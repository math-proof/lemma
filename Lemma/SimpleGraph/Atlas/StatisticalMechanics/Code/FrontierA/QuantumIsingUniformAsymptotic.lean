import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformAsymptotic
open Filter StatMech StatMech.FrontierA


/--
[quantumIsingScaledReducedParameter_cosineInterpolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformAsymptotic.lean)
-/
@[path]
private lemma quantumIsingScaledReducedParameter_cosineInterpolation_eq
  {n : Nat}
  {k : Real}
-- given
  (beta h : Real) :
-- imply
  quantumIsingScaledReducedParameter beta h n k = ((1 + Real.cos k) / 2) * quantumIsingScaledReducedParameter beta h n 0 + ((1 - Real.cos k) / 2) * quantumIsingScaledReducedParameter beta h n Real.pi := by
-- proof
  apply StatMech.FrontierA.quantumIsingScaledReducedParameter_cosineInterpolation beta h n k

/--
[quantumIsingScaledReducedLimit_cosineInterpolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformAsymptotic.lean)
-/
@[path]
private lemma quantumIsingScaledReducedLimit_cosineInterpolation_eq
-- given
  (beta h k : Real) :
-- imply
  quantumIsingScaledReducedLimit beta h k = ((1 + Real.cos k) / 2) * quantumIsingScaledReducedLimit beta h 0 + ((1 - Real.cos k) / 2) * quantumIsingScaledReducedLimit beta h Real.pi := by
-- proof
  apply StatMech.FrontierA.quantumIsingScaledReducedLimit_cosineInterpolation beta h k

/--
[quantumIsingScaledReducedParameter_tendstoUniformly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformAsymptotic.lean)
-/
@[path]
private lemma quantumIsingScaledReducedParameter_tendstoUniformly_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta) :
-- imply
  TendstoUniformly (fun n k ↦ quantumIsingScaledReducedParameter beta h n k) (quantumIsingScaledReducedLimit beta h) atTop := by
-- proof
  apply StatMech.FrontierA.quantumIsingScaledReducedParameter_tendstoUniformly beta h hbeta


-- created on 2026-10-23
