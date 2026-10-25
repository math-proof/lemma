import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.InfinitePairSourceSwitching
open Filter MeasureTheory Topology StatMech StatMech.FrontierB


/--
[pairSource_trace_event_real_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfinitePairSourceSwitching.lean)
-/
@[path]
private lemma pairSource_trace_event_real_tendsto_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y)
  (hQ : IsClopen Q) :
-- imply
  Tendsto (fun k => let j := pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy k ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy j).prod (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy j) : Measure _).real (superposedCurrentTrace ⁻¹' Q)) atTop (nhds (((infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy).prod (infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) : Measure _).real (superposedCurrentTrace ⁻¹' Q))) := by
-- proof
  apply StatMech.FrontierB.pairSource_trace_event_real_tendsto d N beta hbeta x y hx hy hxy Q hQ

/--
[infinitePairSource_free_switching_of_uniqueInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfinitePairSourceSwitching.lean)
-/
@[path]
private lemma infinitePairSource_free_switching_of_uniqueInfiniteCluster_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y)
  (hunique : (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _) (atLeastTwoInfinite d) = 0)
  (hQ : IsClopen Q) :
-- imply
  (∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) ^ 2 * (((infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy).prod (infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) : Measure _).real (superposedCurrentTrace ⁻¹' Q)) = (((infiniteFreeCurrentMeasure d beta hbeta.le).prod (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real (currentPairTraceConnectionGate Q x y)) := by
-- proof
  apply StatMech.FrontierB.infinitePairSource_free_switching_of_uniqueInfiniteCluster d N beta hbeta x y hx hy hxy hunique Q hQ


-- created on 2026-10-23
