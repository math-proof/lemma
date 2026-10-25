import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LocalCurrentTail.Part2
open MeasureTheory StatMech StatMech.FrontierB


/--
[spinProd_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma spinProd_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace V} :
-- imply
  spinProd A s ≤ 1 := by
-- proof
  apply StatMech.FrontierB.spinProd_le_one G A s

/--
[expectationJ_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma expectationJ_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  expectationJ G beta J A ≤ 1 := by
-- proof
  apply StatMech.FrontierB.expectationJ_le_one G beta J A

/--
[currentSum_le_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma currentSum_le_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  currentSum G beta J A ≤ currentSum G beta J ∅ := by
-- proof
  apply StatMech.FrontierB.currentSum_le_empty G beta J hbeta hJ A

/--
[weight_doubledEdgeCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma weight_doubledEdgeCoupling_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : G.edgeFinset}
  {m : EdgeCurrent G} :
-- imply
  weight G beta (doubledEdgeCoupling J e.1) (ofEdgeFun G m) = (2 : ℝ) ^ (m e) * weight G beta J (ofEdgeFun G m) := by
-- proof
  apply StatMech.FrontierB.weight_doubledEdgeCoupling G beta J e m

/--
[doubledEdgeCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma doubledEdgeCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {e f : Sym2 V}
-- given
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  0 ≤ doubledEdgeCoupling J e f := by
-- proof
  apply StatMech.FrontierB.doubledEdgeCoupling_nonneg G J hJ e f

/--
[boltzmannJ_doubledEdgeCoupling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma boltzmannJ_doubledEdgeCoupling_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : G.edgeFinset}
  {s : ConfigSpace V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  boltzmannJ G beta (doubledEdgeCoupling J e.1) s ≤ Real.exp (beta * J e.1) * boltzmannJ G beta J s := by
-- proof
  apply StatMech.FrontierB.boltzmannJ_doubledEdgeCoupling_le G beta J hbeta hJ e s

/--
[partitionJ_doubledEdgeCoupling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma partitionJ_doubledEdgeCoupling_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : G.edgeFinset}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  partitionJ G beta (doubledEdgeCoupling J e.1) ≤ Real.exp (beta * J e.1) * partitionJ G beta J := by
-- proof
  apply StatMech.FrontierB.partitionJ_doubledEdgeCoupling_le G beta J hbeta hJ e

/--
[currentSum_doubledEdgeCoupling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma currentSum_doubledEdgeCoupling_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : G.edgeFinset}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  currentSum G beta (doubledEdgeCoupling J e.1) ∅ ≤ Real.exp (beta * J e.1) * currentSum G beta J ∅ := by
-- proof
  apply StatMech.FrontierB.currentSum_doubledEdgeCoupling_le G beta J hbeta hJ e

/--
[currentWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma currentWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  0 ≤ weight G beta J (ofEdgeFun G m) := by
-- proof
  apply StatMech.FrontierB.currentWeight_nonneg G beta J hbeta hJ m

/--
[sourceless_current_tail_doubling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma sourceless_current_tail_doubling_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  (∑' m : EdgeCurrent G, if sources G (ofEdgeFun G m) = ∅ ∧ K ≤ m e then weight G beta J (ofEdgeFun G m) else 0) ≤ ((2 : ℝ) ^ K)⁻¹ * currentSum G beta (doubledEdgeCoupling J e.1) ∅ := by
-- proof
  apply StatMech.FrontierB.sourceless_current_tail_doubling_le G beta J hbeta hJ e K

/--
[sourcelessCurrentMeasure_edge_exponential_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_edge_exponential_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / (2 : ℝ) ^ K) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_edge_exponential_tail_le G beta J hbeta hJ e K

/--
[nat_le_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma nat_le_two_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ} :
-- imply
  n ≤ 2 ^ n := by
-- proof
  apply StatMech.FrontierB.nat_le_two_pow G n

/--
[sourcelessCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_edge_inverse_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f)
  (hK : 0 < K) :
-- imply
  (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / K) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_edge_inverse_tail_le G beta J hbeta hJ e K hK


-- created on 2026-10-23
