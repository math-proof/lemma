import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.InfinitePlusFreeSourceSwitching
open Filter MeasureTheory Topology StatMech StatMech.FrontierB


/--
[plusFreeSource_trace_event_real_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfinitePlusFreeSourceSwitching.lean)
-/
@[path]
private lemma plusFreeSource_trace_event_real_tendsto_eq
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
  Tendsto (fun k => let j := plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy k ((growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy j).prod (growingFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy j) : Measure _).real (superposedCurrentTrace ⁻¹' Q)) atTop (nhds (((infinitePlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy).prod (infiniteFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) : Measure _).real (superposedCurrentTrace ⁻¹' Q))) := by
-- proof
  apply StatMech.FrontierB.plusFreeSource_trace_event_real_tendsto d N beta hbeta x y hx hy hxy Q hQ

/--
[infinitePlusFreeSource_switching_of_uniqueInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfinitePlusFreeSourceSwitching.lean)
-/
@[path]
private lemma infinitePlusFreeSource_switching_of_uniqueInfiniteCluster_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y)
  (hunique : (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _) (atLeastTwoInfinite d) = 0)
  (hQ : IsClopen Q) :
-- imply
  ((∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) * (∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) * (((infinitePlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy).prod (infiniteFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) : Measure _).real (superposedCurrentTrace ⁻¹' Q)) = (((infinitePlusCurrentMeasure d beta hbeta.le).prod (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real (currentPairTraceConnectionGate Q x y)) := by
-- proof
  apply StatMech.FrontierB.infinitePlusFreeSource_switching_of_uniqueInfiniteCluster d N beta hbeta x y hx hy hxy hunique Q hQ


-- created on 2026-10-23
