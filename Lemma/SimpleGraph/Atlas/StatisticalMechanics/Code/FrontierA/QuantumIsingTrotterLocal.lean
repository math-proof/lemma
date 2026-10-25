import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2
open StatMech StatMech.FrontierA


/--
[quantumIsingSpinSign_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterLocal.lean)
-/
@[path]
private lemma quantumIsingSpinSign_false_eq :
-- imply
  quantumIsingSpinSign false = -1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpinSign_false

/--
[quantumIsingSpinSign_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterLocal.lean)
-/
@[path]
private lemma quantumIsingSpinSign_true_eq :
-- imply
  quantumIsingSpinSign true = 1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpinSign_true

/--
[quantumIsingSpinSign_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterLocal.lean)
-/
@[path]
private lemma quantumIsingSpinSign_mul_self_eq
  {s : Bool} :
-- imply
  quantumIsingSpinSign s * quantumIsingSpinSign s = 1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpinSign_mul_self s

/--
[quantumIsingSpinSign_mul_eq_neg_one_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterLocal.lean)
-/
@[path]
private lemma quantumIsingSpinSign_mul_eq_neg_one_of_ne_eq
  {s t : Bool}
-- given
  (hst : s ≠ t) :
-- imply
  quantumIsingSpinSign s * quantumIsingSpinSign t = -1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpinSign_mul_eq_neg_one_of_ne hst

/--
[quantumIsingTrotterKernel_eq_verticalWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterLocal.lean)
-/
@[path]
private lemma quantumIsingTrotterKernel_eq_verticalWeight_eq
  {n : ℕ}
  {s t : Bool}
-- given
  (beta h : ℝ)
  (hpos : 0 < beta * h / (2 * n)) :
-- imply
  quantumIsingTrotterKernel beta h n s t = Real.exp (-quantumIsingVerticalCoupling beta h n) * Real.exp (quantumIsingVerticalCoupling beta h n * (quantumIsingSpinSign s * quantumIsingSpinSign t)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterKernel_eq_verticalWeight beta h n s t hpos


-- created on 2026-10-23
