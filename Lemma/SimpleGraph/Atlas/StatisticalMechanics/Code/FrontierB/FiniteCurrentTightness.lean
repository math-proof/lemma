import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentTightness
open MeasureTheory StatMech StatMech.FrontierB


/--
[unrestricted_current_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma unrestricted_current_mass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  ∑' m : EdgeCurrent G, weight G beta J (ofEdgeFun G m) = Real.exp (∑ e ∈ G.edgeFinset, beta * J e) := by
-- proof
  apply StatMech.FrontierB.unrestricted_current_mass G beta J hbeta hJ

/--
[summable_nat_mul_wEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma summable_nat_mul_wEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : Sym2 V} :
-- imply
  Summable (fun k : ℕ => (k : ℝ) * wEdge beta J e k) := by
-- proof
  apply StatMech.FrontierB.summable_nat_mul_wEdge G beta J e

/--
[tsum_nat_mul_wEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma tsum_nat_mul_wEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : Sym2 V} :
-- imply
  (∑' k : ℕ, (k : ℝ) * wEdge beta J e k) = (beta * J e) * Real.exp (beta * J e) := by
-- proof
  apply StatMech.FrontierB.tsum_nat_mul_wEdge G beta J e

/--
[sources_zero_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma sources_zero_current_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  sources G (ofEdgeFun G (0 : EdgeCurrent G)) = ∅ := by
-- proof
  apply StatMech.FrontierB.sources_zero_current G

/--
[one_le_currentSum_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma one_le_currentSum_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  1 ≤ currentSum G beta J ∅ := by
-- proof
  apply StatMech.FrontierB.one_le_currentSum_empty G beta J hbeta hJ

/--
[unrestricted_current_first_moment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma unrestricted_current_first_moment_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : ↑G.edgeFinset}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  ∑' m : EdgeCurrent G, (m e : ℝ) * weight G beta J (ofEdgeFun G m) = (beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g) := by
-- proof
  apply StatMech.FrontierB.unrestricted_current_first_moment G beta J hbeta hJ e

/--
[summable_unrestricted_current_first_moment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma summable_unrestricted_current_first_moment_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : ↑G.edgeFinset}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  Summable (fun m : EdgeCurrent G => (m e : ℝ) * weight G beta J (ofEdgeFun G m)) := by
-- proof
  apply StatMech.FrontierB.summable_unrestricted_current_first_moment G beta J hbeta hJ e

/--
[unrestricted_current_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma unrestricted_current_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : ↑G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hK : 0 < K) :
-- imply
  (∑' m : EdgeCurrent G, if K ≤ m e then weight G beta J (ofEdgeFun G m) else 0) ≤ ((beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g)) / K := by
-- proof
  apply StatMech.FrontierB.unrestricted_current_tail_le G beta J hbeta hJ e K hK

/--
[sourcelessCurrentMeasure_edge_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_edge_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : ↑G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hK : 0 < K) :
-- imply
  (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m | K ≤ m e} ≤ ENNReal.ofReal (((beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g)) / K) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_edge_tail_le G beta J hbeta hJ e K hK

/--
[sourcelessCurrentMeasure_edge_tail_le_of_total_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_edge_tail_le_of_total_coupling_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {C : ℝ}
  {e : ↑G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hC : ∑ g ∈ G.edgeFinset, beta * J g ≤ C)
  (hK : 0 < K) :
-- imply
  (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m | K ≤ m e} ≤ ENNReal.ofReal ((C * Real.exp C) / K) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_edge_tail_le_of_total_coupling G beta J hbeta hJ C hC e K hK

/--
[sourcelessCurrentMeasure_finite_edges_tail_le_of_total_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentTightness.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_finite_edges_tail_le_of_total_coupling_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {C : ℝ}
  {S : Finset (↑G.edgeFinset)}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hC : ∑ g ∈ G.edgeFinset, beta * J g ≤ C)
  (hK : 0 < K) :
-- imply
  (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m | ∃ e ∈ S, K ≤ m e} ≤ S.card * ENNReal.ofReal ((C * Real.exp C) / K) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_finite_edges_tail_le_of_total_coupling G beta J hbeta hJ C hC S K hK


-- created on 2026-10-23
