import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbolBounds
open StatMech StatMech.FrontierA


/--
[triangular_cosine_combination_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbolBounds.lean)
-/
@[path]
private lemma triangular_cosine_combination_le_eq
  {a b : ℝ}
  {p q : ℝ}
-- given
  (ha : 0 < a)
  (hb : b < 0) :
-- imply
  a * (Real.cos p + Real.cos q) + b * Real.cos (p + q) ≤ -a ^ 2 / (2 * b) - b := by
-- proof
  apply StatMech.FrontierA.triangular_cosine_combination_le ha hb p q

/--
[triangularIsingSymbol_equal_couplings_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbolBounds.lean)
-/
@[path]
private lemma triangularIsingSymbol_equal_couplings_lower_eq
  {x y : ℝ}
  {p q : ℝ}
-- given
  (hx : 0 < x)
  (hy : y < 0) :
-- imply
  Real.cosh (2 * x) ^ 2 * Real.cosh (2 * y) + Real.sinh (2 * x) ^ 2 * Real.sinh (2 * y) + Real.sinh (2 * x) ^ 2 / (2 * Real.sinh (2 * y)) + Real.sinh (2 * y) ≤ triangularIsingSymbol x x y p q := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_equal_couplings_lower hx hy p q

/--
[triangular_hyperbolic_lower_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbolBounds.lean)
-/
@[path]
private lemma triangular_hyperbolic_lower_pos_eq
  {x y : ℝ}
-- given
  (hx : 0 < x)
  (hy : y ≤ -x) :
-- imply
  0 < Real.cosh x ^ 2 * Real.cosh y + Real.sinh x ^ 2 * Real.sinh y + Real.sinh x ^ 2 / (2 * Real.sinh y) + Real.sinh y := by
-- proof
  apply StatMech.FrontierA.triangular_hyperbolic_lower_pos hx hy

/--
[triangularIsingSymbol_pos_of_third_le_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbolBounds.lean)
-/
@[path]
private lemma triangularIsingSymbol_pos_of_third_le_neg_eq
  {x y : ℝ}
  {p q : ℝ}
-- given
  (hx : 0 < x)
  (hy : y ≤ -x) :
-- imply
  0 < triangularIsingSymbol x x y p q := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_pos_of_third_le_neg hx hy p q

/--
[continuous_log_triangularIsingSymbol_third_le_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbolBounds.lean)
-/
@[path]
private lemma continuous_log_triangularIsingSymbol_third_le_neg_eq
  {x y : ℝ}
-- given
  (hx : 0 < x)
  (hy : y ≤ -x) :
-- imply
  Continuous fun p : ℝ × ℝ => Real.log (triangularIsingSymbol x x y p.1 p.2) := by
-- proof
  apply StatMech.FrontierA.continuous_log_triangularIsingSymbol_third_le_neg hx hy

/--
[triangularIsingSymbol_riemann_tendsto_symmetric_third_le_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbolBounds.lean)
-/
@[path]
private lemma triangularIsingSymbol_riemann_tendsto_symmetric_third_le_neg_eq
  {x y : ℝ}
-- given
  (hx : 0 < x)
  (hy : y ≤ -x) :
-- imply
  Filter.Tendsto (fun L : ℕ => (2 * Real.pi / L) ^ 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, Real.log (triangularIsingSymbol x x y (2 * Real.pi * i / L) (2 * Real.pi * j / L))) Filter.atTop (nhds (∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol x x y k1 k2))) := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_riemann_tendsto_symmetric_third_le_neg hx hy


-- created on 2026-10-23
