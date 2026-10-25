import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
open MeasureTheory StatMech StatMech.FrontierB


/--
[summable_parityEdgeKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean)
-/
@[path]
private lemma summable_parityEdgeKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {odd : Bool} :
-- imply
  Summable (parityEdgeKernel beta odd) := by
-- proof
  apply StatMech.FrontierB.summable_parityEdgeKernel G beta odd

/--
[parityEdgeKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean)
-/
@[path]
private lemma parityEdgeKernel_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {odd : Bool}
  {k : ℕ}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 ≤ parityEdgeKernel beta odd k := by
-- proof
  apply StatMech.FrontierB.parityEdgeKernel_nonneg G beta hbeta odd k

/--
[tsum_parityEdgeKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean)
-/
@[path]
private lemma tsum_parityEdgeKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {odd : Bool}
-- given
  (hbeta : 0 < beta) :
-- imply
  ∑' k : ℕ, parityEdgeKernel beta odd k = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_parityEdgeKernel G beta hbeta odd

/--
[tsum_parityCurrentKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean)
-/
@[path]
private lemma tsum_parityCurrentKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta) :
-- imply
  ∑' m : EdgeCurrent G, parityCurrentKernel G beta H m = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_parityCurrentKernel G beta hbeta H

/--
[parityFiberMass_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean)
-/
@[path]
private lemma parityFiberMass_closed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta)
  (hH : H ⊆ G.edgeFinset) :
-- imply
  parityFiberMass G beta H = Real.cosh beta ^ G.edgeFinset.card * Real.tanh beta ^ H.card := by
-- proof
  apply StatMech.FrontierB.parityFiberMass_closed G beta hbeta H hH

/--
[weight_eq_parityFiberMass_mul_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean)
-/
@[path]
private lemma weight_eq_parityFiberMass_mul_kernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hH : H ⊆ G.edgeFinset)
  (hm : currentParitySupport G m = H) :
-- imply
  weight G beta (fun _ => 1) (ofEdgeFun G m) = parityFiberMass G beta H * parityCurrentKernel G beta H m := by
-- proof
  apply StatMech.FrontierB.weight_eq_parityFiberMass_mul_kernel G beta hbeta H hH m hm


-- created on 2026-10-23
