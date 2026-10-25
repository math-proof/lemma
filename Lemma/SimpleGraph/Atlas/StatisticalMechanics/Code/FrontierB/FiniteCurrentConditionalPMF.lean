import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
open MeasureTheory StatMech StatMech.FrontierB


/--
[summable_parityCurrentKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma summable_parityCurrentKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta) :
-- imply
  Summable (parityCurrentKernel G beta H) := by
-- proof
  apply StatMech.FrontierB.summable_parityCurrentKernel G beta hbeta H

/--
[tsum_ofReal_parityCurrentKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_ofReal_parityCurrentKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta) :
-- imply
  ∑' m : EdgeCurrent G, ENNReal.ofReal (parityCurrentKernel G beta H m) = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_ofReal_parityCurrentKernel G beta hbeta H

/--
[parityCurrentPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma parityCurrentPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta) :
-- imply
  parityCurrentPMF G beta hbeta H m = ENNReal.ofReal (parityCurrentKernel G beta H m) := by
-- proof
  apply StatMech.FrontierB.parityCurrentPMF_apply G beta hbeta H m

/--
[parityCurrentKernel_eq_zero_of_support_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma parityCurrentKernel_eq_zero_of_support_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (hH : H ⊆ G.edgeFinset)
  (hm : currentParitySupport G m ≠ H) :
-- imply
  parityCurrentKernel G beta H m = 0 := by
-- proof
  apply StatMech.FrontierB.parityCurrentKernel_eq_zero_of_support_ne G beta H hH m hm

/--
[sourcelessCurrentPMF_apply_eq_parity_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessCurrentPMF_apply_eq_parity_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta) :
-- imply
  sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) m = freeParityPMF G beta hbeta.le (currentParitySupport G m) * parityCurrentPMF G beta hbeta (currentParitySupport G m) m := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentPMF_apply_eq_parity_factor G beta hbeta m

/--
[sourcelessCurrentPMF_eq_parity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessCurrentPMF_eq_parity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) = (freeParityPMF G beta hbeta.le).bind (parityCurrentPMF G beta hbeta) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentPMF_eq_parity_bind G beta hbeta

/--
[sourcelessCurrentPMF_map_eq_parity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessCurrentPMF_map_eq_parity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {f : EdgeCurrent G → A}
-- given
  (hbeta : 0 < beta) :
-- imply
  PMF.map f (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one)) = (freeParityPMF G beta hbeta.le).bind (fun H => PMF.map f (parityCurrentPMF G beta hbeta H)) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentPMF_map_eq_parity_bind G beta hbeta f

/--
[sourcelessCurrentFiniteMarginal_eq_parity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessCurrentFiniteMarginal_eq_parity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta) :
-- imply
  PMF.map (restrictCurrent S) (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one)) = (freeParityPMF G beta hbeta.le).bind (fun H => PMF.map (restrictCurrent S) (parityCurrentPMF G beta hbeta H)) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentFiniteMarginal_eq_parity_bind G beta hbeta S

/--
[summable_finiteParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma summable_finiteParityKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {S : Finset E}
  {beta : ℝ}
  {odd : ↑S → Bool}
-- given
  (hbeta : 0 < beta) :
-- imply
  Summable (finiteParityKernel S beta odd) := by
-- proof
  apply StatMech.FrontierB.summable_finiteParityKernel G S beta hbeta odd

/--
[tsum_ofReal_finiteParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_ofReal_finiteParityKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {S : Finset E}
  {beta : ℝ}
  {odd : ↑S → Bool}
-- given
  (hbeta : 0 < beta) :
-- imply
  ∑' a : ↑S → ℕ, ENNReal.ofReal (finiteParityKernel S beta odd a) = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_ofReal_finiteParityKernel G S beta hbeta odd

/--
[finiteParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma finiteParityPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {S : Finset E}
  {beta : ℝ}
  {odd : ↑S → Bool}
  {a : ↑S → ℕ}
-- given
  (hbeta : 0 < beta) :
-- imply
  finiteParityPMF S beta hbeta odd a = ENNReal.ofReal (finiteParityKernel S beta odd a) := by
-- proof
  apply StatMech.FrontierB.finiteParityPMF_apply G S beta hbeta odd a

/--
[tsum_ofReal_fintypeParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_ofReal_fintypeParityKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype I]
  [DecidableEq I]
  {beta : ℝ}
  {odd : I → Bool}
-- given
  (hbeta : 0 < beta) :
-- imply
  ∑' a : I → ℕ, ENNReal.ofReal (∏ i, parityEdgeKernel beta (odd i) (a i)) = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_ofReal_fintypeParityKernel G beta hbeta odd

/--
[parityCurrentPMF_map_restrictCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma parityCurrentPMF_map_restrictCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta) :
-- imply
  PMF.map (restrictCurrent S) (parityCurrentPMF G beta hbeta H) = finiteParityPMF S beta hbeta (fun e : ↑S => e.1.1 ∈ H) := by
-- proof
  apply StatMech.FrontierB.parityCurrentPMF_map_restrictCurrent G G beta hbeta H S

/--
[sourcelessCurrentFiniteMarginal_eq_localParity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessCurrentFiniteMarginal_eq_localParity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta) :
-- imply
  PMF.map (restrictCurrent S) (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one)) = (PMF.map (restrictParity G S) (freeParityPMF G beta hbeta.le)).bind (finiteParityPMF S beta hbeta) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentFiniteMarginal_eq_localParity_bind G G beta hbeta S


-- created on 2026-10-23
