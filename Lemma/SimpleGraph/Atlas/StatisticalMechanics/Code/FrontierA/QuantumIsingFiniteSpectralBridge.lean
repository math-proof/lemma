import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteSpectralBridge.Part2
open StatMech StatMech.FrontierA


/--
[quantumIsingVerticalNormalization_mul_symbol_eq_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteSpectralBridge.lean)
-/
@[path]
private lemma quantumIsingVerticalNormalization_mul_symbol_eq_reduced_eq
  {n : Nat}
  {k q : Real}
-- given
  (beta h : Real)
  (hx : 0 < beta * h / (2 * n))
  (hx1 : beta * h / (2 * n) < 1) :
-- imply
  4 * Real.exp (-2 * quantumIsingVerticalCoupling beta h n) * triangularIsingSymbol (beta / (4 * n)) (quantumIsingVerticalCoupling beta h n) 0 (k + Real.pi) q = 2 * (1 - (beta * h / (2 * n)) ^ 2) * (quantumIsingTrotterReducedParameter beta h n k - Real.cos q) := by
-- proof
  apply StatMech.FrontierA.quantumIsingVerticalNormalization_mul_symbol_eq_reduced beta h n k q hx hx1

/--
[two_mul_quantumIsingNormalizedClassicalPartition_eq_sectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteSpectralBridge.lean)
-/
@[path]
private lemma two_mul_quantumIsingNormalizedClassicalPartition_eq_sectors_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real) :
-- imply
  (2 : Complex) * (Real.exp (-quantumIsingVerticalCoupling beta h L) ^ (L * L) * quantumIsingClassicalCylinderPartition beta h L L : Real) = quantumIsingNormalizedSpinSector beta h L 1 1 + quantumIsingNormalizedSpinSector beta h L 0 1 + quantumIsingNormalizedSpinSector beta h L 1 0 - quantumIsingNormalizedSpinSector beta h L 0 0 := by
-- proof
  apply StatMech.FrontierA.two_mul_quantumIsingNormalizedClassicalPartition_eq_sectors beta h L

/--
[quantumIsingNormalizedSpinSector_sq_eq_symbolProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteSpectralBridge.lean)
-/
@[path]
private lemma quantumIsingNormalizedSpinSector_sq_eq_symbolProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {a b : Fin 2}
-- given
  (beta h : Real) :
-- imply
  quantumIsingNormalizedSpinSector beta h L a b ^ 2 = ∏ j : ZMod L × ZMod L, (4 * Real.exp (-2 * quantumIsingVerticalCoupling beta h L) * triangularIsingSymbol (beta / (4 * L)) (quantumIsingVerticalCoupling beta h L) 0 (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L) (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedSpinSector_sq_eq_symbolProduct beta h L a b

/--
[quantumIsingNormalizedSpinSector_sq_eq_reducedProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteSpectralBridge.lean)
-/
@[path]
private lemma quantumIsingNormalizedSpinSector_sq_eq_reducedProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {a b : Fin 2}
-- given
  (beta h : Real)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  quantumIsingNormalizedSpinSector beta h L a b ^ 2 = ∏ j : ZMod L × ZMod L, (2 * (1 - (beta * h / (2 * L)) ^ 2) * (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L - Real.pi) - Real.cos (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) : Complex) := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedSpinSector_sq_eq_reducedProduct beta h L a b hx hx1


-- created on 2026-10-23
