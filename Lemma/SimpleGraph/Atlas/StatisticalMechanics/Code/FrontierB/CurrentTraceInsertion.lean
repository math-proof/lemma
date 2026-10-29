import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceInsertion.Part4
open MeasureTheory StatMech StatMech.FrontierB


/--
[zeroCurrentEdge_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma zeroCurrentEdge_apply_same_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G} :
-- imply
  zeroCurrentEdge G e m e = 0 := by
-- proof
  apply StatMech.FrontierB.zeroCurrentEdge_apply_same G e m

/--
[zeroCurrentEdge_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma zeroCurrentEdge_apply_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e f : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hfe : f ≠ e) :
-- imply
  zeroCurrentEdge G e m f = m f := by
-- proof
  apply StatMech.FrontierB.zeroCurrentEdge_apply_of_ne G e f hfe m

/--
[forceCurrentEdgePositive_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_apply_same_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G} :
-- imply
  forceCurrentEdgePositive G e m e = if m e = 0 then 2 else m e := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_apply_same G e m

/--
[forceCurrentEdgePositive_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_apply_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e f : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hfe : f ≠ e) :
-- imply
  forceCurrentEdgePositive G e m f = m f := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_apply_of_ne G e f hfe m

/--
[forceCurrentEdgePositive_eq_self_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_eq_self_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G} :
-- imply
  forceCurrentEdgePositive G e m = m ↔ m e ≠ 0 := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_eq_self_iff G e m

/--
[forceCurrentEdgePositive_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G} :
-- imply
  forceCurrentEdgePositive G e m e ≠ 0 := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_ne_zero G e m

/--
[forceCurrentEdgePositive_zeroCurrentEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_zeroCurrentEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G} :
-- imply
  forceCurrentEdgePositive G e (zeroCurrentEdge G e m) = Function.update m e 2 := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_zeroCurrentEdge G e m

/--
[forceCurrentEdgePositive_preimage_iff_of_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_preimage_iff_of_eq_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m a : EdgeCurrent G}
-- given
  (hm : m e = 2) :
-- imply
  forceCurrentEdgePositive G e a = m <-> a = m \/ a = zeroCurrentEdge G e m := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_preimage_iff_of_eq_two G e m a hm

/--
[forceCurrentEdgePositive_preimage_iff_of_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_preimage_iff_of_ne_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m a : EdgeCurrent G}
-- given
  (hm0 : m e ≠ 0)
  (hm2 : m e ≠ 2) :
-- imply
  forceCurrentEdgePositive G e a = m ↔ a = m := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_preimage_iff_of_ne_two G e m a hm0 hm2

/--
[forceCurrentEdgePositive_no_preimage_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_no_preimage_of_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m a : EdgeCurrent G}
-- given
  (hm : m e = 0) :
-- imply
  forceCurrentEdgePositive G e a ≠ m := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_no_preimage_of_eq_zero G e m a hm

/--
[sources_twoFluxAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma sources_twoFluxAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset} :
-- imply
  sources G (ofEdgeFun G (twoFluxAt G e)) = ∅ := by
-- proof
  apply StatMech.FrontierB.sources_twoFluxAt G e

/--
[forceCurrentEdgePositive_eq_add_twoFluxAt_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceCurrentEdgePositive_eq_add_twoFluxAt_of_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm : m e = 0) :
-- imply
  forceCurrentEdgePositive G e m = fun f => m f + twoFluxAt G e f := by
-- proof
  apply StatMech.FrontierB.forceCurrentEdgePositive_eq_add_twoFluxAt_of_zero G e m hm

/--
[sources_forceCurrentEdgePositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma sources_forceCurrentEdgePositive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G} :
-- imply
  sources G (ofEdgeFun G (forceCurrentEdgePositive G e m)) = sources G (ofEdgeFun G m) := by
-- proof
  apply StatMech.FrontierB.sources_forceCurrentEdgePositive G e m

/--
[weight_forceCurrentEdgePositive_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma weight_forceCurrentEdgePositive_of_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm : m e = 0) :
-- imply
  weight G beta (fun _ => 1) (ofEdgeFun G (forceCurrentEdgePositive G e m)) = weight G beta (fun _ => 1) (ofEdgeFun G m) * (beta ^ 2 / 2) := by
-- proof
  apply StatMech.FrontierB.weight_forceCurrentEdgePositive_of_zero G beta e m hm

/--
[currentPMF_forceCurrentEdgePositive_apply_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma currentPMF_forceCurrentEdgePositive_apply_of_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hA : 0 < currentSum G beta (fun _ => 1) A)
  (hm : m e = 0) :
-- imply
  currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA (forceCurrentEdgePositive G e m) = ENNReal.ofReal (beta ^ 2 / 2) * currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA m := by
-- proof
  apply StatMech.FrontierB.currentPMF_forceCurrentEdgePositive_apply_of_zero G beta hbeta A hA e m hm

/--
[boundaryCurrentPMF_forceCurrentEdgePositive_apply_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma boundaryCurrentPMF_forceCurrentEdgePositive_apply_of_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hm : m e = 0) :
-- imply
  boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior (forceCurrentEdgePositive G e m) = ENNReal.ofReal (beta ^ 2 / 2) * boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior m := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_forceCurrentEdgePositive_apply_of_zero G beta hbeta interior e m hm

/--
[PMF.map_forceCurrentEdgePositive_apply_of_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma map_forceCurrentEdgePositive_apply_of_eq_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : PMF (EdgeCurrent G)}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm : m e = 2) :
-- imply
  PMF.map (forceCurrentEdgePositive G e) p m = p m + p (zeroCurrentEdge G e m) := by
-- proof
  apply StatMech.FrontierB.PMF.map_forceCurrentEdgePositive_apply_of_eq_two G p e m hm

/--
[PMF.map_forceCurrentEdgePositive_apply_of_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma map_forceCurrentEdgePositive_apply_of_ne_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : PMF (EdgeCurrent G)}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm0 : m e ≠ 0)
  (hm2 : m e ≠ 2) :
-- imply
  PMF.map (forceCurrentEdgePositive G e) p m = p m := by
-- proof
  apply StatMech.FrontierB.PMF.map_forceCurrentEdgePositive_apply_of_ne_two G p e m hm0 hm2

/--
[PMF.map_forceCurrentEdgePositive_apply_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma map_forceCurrentEdgePositive_apply_of_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : PMF (EdgeCurrent G)}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm : m e = 0) :
-- imply
  PMF.map (forceCurrentEdgePositive G e) p m = 0 := by
-- proof
  apply StatMech.FrontierB.PMF.map_forceCurrentEdgePositive_apply_of_eq_zero G p e m hm

/--
[currentTraceInsertionConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma currentTraceInsertionConstant_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 < currentTraceInsertionConstant beta := by
-- proof
  apply StatMech.FrontierB.currentTraceInsertionConstant_pos G hbeta

/--
[currentTraceInsertionConstant_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma currentTraceInsertionConstant_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ} :
-- imply
  currentTraceInsertionConstant beta ≤ 1 := by
-- proof
  apply StatMech.FrontierB.currentTraceInsertionConstant_le_one G beta

/--
[currentPMF_map_forceCurrentEdgePositive_apply_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma currentPMF_map_forceCurrentEdgePositive_apply_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hA : 0 < currentSum G beta (fun _ => 1) A) :
-- imply
  ENNReal.ofReal (currentTraceInsertionConstant beta) * PMF.map (forceCurrentEdgePositive G e) (currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA) m ≤ currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA m := by
-- proof
  apply StatMech.FrontierB.currentPMF_map_forceCurrentEdgePositive_apply_bound G beta hbeta A hA e m

/--
[boundaryCurrentPMF_map_forceCurrentEdgePositive_apply_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma boundaryCurrentPMF_map_forceCurrentEdgePositive_apply_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta) :
-- imply
  ENNReal.ofReal (currentTraceInsertionConstant beta) * PMF.map (forceCurrentEdgePositive G e) (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior) m ≤ boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior m := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_map_forceCurrentEdgePositive_apply_bound G beta hbeta interior e m

/--
[PMF.toMeasure_map_le_of_apply_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma toMeasure_map_le_of_apply_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [MeasurableSpace alpha]
  [MeasurableSingletonClass alpha]
  {p : PMF alpha}
  {f : alpha → alpha}
  {S : Set alpha}
-- given
  (c : ENNReal)
  (hpoint : ∀ a, c * PMF.map f p a ≤ p a) :
-- imply
  c * (PMF.map f p).toMeasure S ≤ p.toMeasure S := by
-- proof
  apply StatMech.FrontierB.PMF.toMeasure_map_le_of_apply_le G p f c hpoint S

/--
[currentPMF_forceCurrentEdgePositive_event_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma currentPMF_forceCurrentEdgePositive_event_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
  {e : G.edgeFinset}
  {S : Set (EdgeCurrent G)}
-- given
  (hbeta : 0 < beta)
  (hA : 0 < currentSum G beta (fun _ => 1) A) :
-- imply
  ENNReal.ofReal (currentTraceInsertionConstant beta) * (PMF.map (forceCurrentEdgePositive G e) (currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA)).toMeasure S ≤ (currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA).toMeasure S := by
-- proof
  apply StatMech.FrontierB.currentPMF_forceCurrentEdgePositive_event_bound G beta hbeta A hA e S

/--
[boundaryCurrentPMF_forceCurrentEdgePositive_event_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma boundaryCurrentPMF_forceCurrentEdgePositive_event_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {e : G.edgeFinset}
  {S : Set (EdgeCurrent G)}
-- given
  (hbeta : 0 < beta) :
-- imply
  ENNReal.ofReal (currentTraceInsertionConstant beta) * (PMF.map (forceCurrentEdgePositive G e) (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior)).toMeasure S ≤ (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior).toMeasure S := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_forceCurrentEdgePositive_event_bound G beta hbeta interior e S

/--
[forceInfiniteCurrentEdgePositive_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceInfiniteCurrentEdgePositive_apply_same_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {e : E}
  {m : InfiniteCurrentConfig E} :
-- imply
  forceInfiniteCurrentEdgePositive e m e = if m e = 0 then 2 else m e := by
-- proof
  apply StatMech.FrontierB.forceInfiniteCurrentEdgePositive_apply_same G e m

/--
[forceInfiniteCurrentEdgePositive_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceInfiniteCurrentEdgePositive_apply_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {e f : E}
  {m : InfiniteCurrentConfig E}
-- given
  (hfe : f ≠ e) :
-- imply
  forceInfiniteCurrentEdgePositive e m f = m f := by
-- proof
  apply StatMech.FrontierB.forceInfiniteCurrentEdgePositive_apply_of_ne G e f hfe m

/--
[continuous_forceInfiniteCurrentEdgePositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma continuous_forceInfiniteCurrentEdgePositive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {e : E} :
-- imply
  Continuous (forceInfiniteCurrentEdgePositive e : InfiniteCurrentConfig E → InfiniteCurrentConfig E) := by
-- proof
  apply StatMech.FrontierB.continuous_forceInfiniteCurrentEdgePositive G e

/--
[currentTrace_forceInfiniteCurrentEdgePositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma currentTrace_forceInfiniteCurrentEdgePositive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {e : E}
  {m : InfiniteCurrentConfig E} :
-- imply
  currentTrace (forceInfiniteCurrentEdgePositive e m) = setOpen e (currentTrace m) := by
-- proof
  apply StatMech.FrontierB.currentTrace_forceInfiniteCurrentEdgePositive G e m

/--
[superposedCurrentTrace_forceInfiniteCurrentEdgePositive_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma superposedCurrentTrace_forceInfiniteCurrentEdgePositive_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {e : E}
  {m n : InfiniteCurrentConfig E} :
-- imply
  superposedCurrentTrace (forceInfiniteCurrentEdgePositive e m, n) = setOpen e (superposedCurrentTrace (m, n)) := by
-- proof
  apply StatMech.FrontierB.superposedCurrentTrace_forceInfiniteCurrentEdgePositive_fst G e m n

/--
[forceInfiniteCurrentEdgePositive_extendBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma forceInfiniteCurrentEdgePositive_extendBoxCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : ℕ}
  {e : (StatMech.FK.boxGraph d n).edgeFinset}
  {m : EdgeCurrent (StatMech.FK.boxGraph d n)} :
-- imply
  forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) (extendBoxCurrent d n m) = extendBoxCurrent d n (forceCurrentEdgePositive (StatMech.FK.boxGraph d n) e m) := by
-- proof
  apply StatMech.FrontierB.forceInfiniteCurrentEdgePositive_extendBoxCurrent G d n e m

/--
[freeBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : ℕ}
  {beta : ℝ}
  {e : (StatMech.FK.boxGraph d n).edgeFinset}
  {S : Set (InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hS : MeasurableSet S) :
-- imply
  ENNReal.ofReal (currentTraceInsertionConstant beta) * (freeBoxCurrentMeasure d n beta hbeta.le : Measure _) (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤ (freeBoxCurrentMeasure d n beta hbeta.le : Measure _) S := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound G d n beta hbeta e S hS

/--
[plusBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : ℕ}
  {beta : ℝ}
  {e : (StatMech.FK.boxGraph d n).edgeFinset}
  {S : Set (InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hS : MeasurableSet S) :
-- imply
  ENNReal.ofReal (currentTraceInsertionConstant beta) * (plusBoxCurrentMeasure d n beta hbeta.le : Measure _) (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤ (plusBoxCurrentMeasure d n beta hbeta.le : Measure _) S := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound G d n beta hbeta e S hS

/--
[eventually_boxCurrentEdgeIncl_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma eventually_boxCurrentEdgeIncl_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {e : Sym2 (Site d)}
-- given
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  ∀ᶠ n in Filter.atTop, ∃ eb : (StatMech.FK.boxGraph d n).edgeFinset, boxCurrentEdgeIncl d n eb = e := by
-- proof
  apply StatMech.FrontierB.eventually_boxCurrentEdgeIncl_eq G d e he

/--
[infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
  {C : Set (InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet)
  (hC : IsClopen C) :
-- imply
  ENNReal.ofReal (currentTraceInsertionConstant beta) * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _) (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤ (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _) C := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound G d beta hbeta e he C hC

/--
[infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
  {C : Set (InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet)
  (hC : IsClopen C) :
-- imply
  ENNReal.ofReal (currentTraceInsertionConstant beta) * (infinitePlusCurrentMeasure d beta hbeta.le : Measure _) (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤ (infinitePlusCurrentMeasure d beta hbeta.le : Measure _) C := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound G d beta hbeta e he C hC

/--
[isClopen_of_mem_currentMeasurableCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma isClopen_of_mem_currentMeasurableCylinders_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : Set (InfiniteCurrentConfig E)}
-- given
  (hC : C ∈ measurableCylinders (fun _ : E => ℕ)) :
-- imply
  IsClopen C := by
-- proof
  apply StatMech.FrontierB.isClopen_of_mem_currentMeasurableCylinders G C hC

/--
[infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
  {C : Set (InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => ℕ)) :
-- imply
  currentTraceInsertionConstant beta * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤ (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real C := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound G d beta hbeta e he C hC

/--
[infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
  {C : Set (InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => ℕ)) :
-- imply
  currentTraceInsertionConstant beta * (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤ (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real C := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound G d beta hbeta e he C hC

/--
[currentModification_bound_of_cylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma currentModification_bound_of_cylinders_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Countable E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
  {f : InfiniteCurrentConfig E → InfiniteCurrentConfig E}
  {c : ℝ}
  {A : Set (InfiniteCurrentConfig E)}
-- given
  (hf : Measurable f)
  (hc : 0 ≤ c)
  (hcyl : ∀ C ∈ measurableCylinders (fun _ : E => ℕ), c * mu.real (f ⁻¹' C) ≤ mu.real C)
  (hA : MeasurableSet A) :
-- imply
  c * mu.real (f ⁻¹' A) ≤ mu.real A := by
-- proof
  apply StatMech.FrontierB.currentModification_bound_of_cylinders G mu f hf c hc hcyl A hA

/--
[infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).map (forceInfiniteCurrentEdgePositive e) ≪ (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous G d beta hbeta e he

/--
[infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).map (forceInfiniteCurrentEdgePositive e) ≪ (infinitePlusCurrentMeasure d beta hbeta.le : Measure _) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous G d beta hbeta e he

/--
[independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Countable E]
  [DecidableEq E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {e : E}
-- given
  (hmu : (mu : Measure _).map (forceInfiniteCurrentEdgePositive e) ≪ (mu : Measure _)) :
-- imply
  (independentSuperposedTraceLaw mu nu : Measure _).map (setOpen e) ≪ (independentSuperposedTraceLaw mu nu : Measure _) := by
-- proof
  apply StatMech.FrontierB.independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst G mu nu e hmu

/--
[freeFreeSuperposedTraceLaw_setOpen_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma freeFreeSuperposedTraceLaw_setOpen_absolutelyContinuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).map (setOpen e) ≪ (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _) := by
-- proof
  apply StatMech.FrontierB.freeFreeSuperposedTraceLaw_setOpen_absolutelyContinuous G d beta hbeta e he

/--
[freePlusSuperposedTraceLaw_setOpen_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_setOpen_absolutelyContinuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _).map (setOpen e) ≪ (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_setOpen_absolutelyContinuous G d beta hbeta e he

/--
[plusPlusSuperposedTraceLaw_setOpen_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma plusPlusSuperposedTraceLaw_setOpen_absolutelyContinuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hbeta : 0 < beta)
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _).map (setOpen e) ≪ (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) := by
-- proof
  apply StatMech.FrontierB.plusPlusSuperposedTraceLaw_setOpen_absolutelyContinuous G d beta hbeta e he

/--
[hasLatticeFiniteEnergyMerge_of_singleOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma hasLatticeFiniteEnergyMerge_of_singleOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hone : ∀ e : Sym2 (Site d), e ∈ (hypercubicLattice d).edgeSet → mu.map (setOpen e) ≪ mu) :
-- imply
  HasLatticeFiniteEnergyMerge mu := by
-- proof
  apply StatMech.FrontierB.hasLatticeFiniteEnergyMerge_of_singleOpen G mu hone

/--
[freeFreeSuperposedTraceLaw_hasLatticeFiniteEnergyMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma freeFreeSuperposedTraceLaw_hasLatticeFiniteEnergyMerge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  HasLatticeFiniteEnergyMerge (d := d) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _) := by
-- proof
  apply StatMech.FrontierB.freeFreeSuperposedTraceLaw_hasLatticeFiniteEnergyMerge G d beta hbeta

/--
[freePlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  HasLatticeFiniteEnergyMerge (d := d) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge G d beta hbeta

/--
[plusPlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean)
-/
@[path]
private lemma plusPlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  HasLatticeFiniteEnergyMerge (d := d) (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) := by
-- proof
  apply StatMech.FrontierB.plusPlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge G d beta hbeta


-- created on 2026-10-23
