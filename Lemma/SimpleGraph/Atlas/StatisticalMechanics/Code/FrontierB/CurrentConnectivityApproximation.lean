import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentConnectivityApproximation
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[boxConnectionEvent_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma boxConnectionEvent_mono_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  Monotone (fun n => boxConnectionEvent n x y) := by
-- proof
  apply StatMech.FrontierB.boxConnectionEvent_mono x y

/--
[mem_iUnion_boxConnectionEvent_iff_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma mem_iUnion_boxConnectionEvent_iff_connected_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  omega ∈ (⋃ n, boxConnectionEvent n x y) ↔ Connected d omega x y := by
-- proof
  apply StatMech.FrontierB.mem_iUnion_boxConnectionEvent_iff_connected omega x y

/--
[iUnion_boxConnectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma iUnion_boxConnectionEvent_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  (⋃ n, boxConnectionEvent n x y) = {omega | Connected d omega x y} := by
-- proof
  apply StatMech.FrontierB.iUnion_boxConnectionEvent x y

/--
[isClopen_boxConnectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma isClopen_boxConnectionEvent_eq
  {d : ℕ}
  {n : ℕ}
  {x y : Site d} :
-- imply
  IsClopen (boxConnectionEvent n x y) := by
-- proof
  apply StatMech.FrontierB.isClopen_boxConnectionEvent n x y

/--
[isClopen_currentPairBoxConnectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma isClopen_currentPairBoxConnectionEvent_eq
  {d : ℕ}
  {n : ℕ}
  {x y : Site d} :
-- imply
  IsClopen (currentPairBoxConnectionEvent n x y) := by
-- proof
  apply StatMech.FrontierB.isClopen_currentPairBoxConnectionEvent n x y

/--
[currentPairBoxConnectionEvent_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma currentPairBoxConnectionEvent_mono_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  Monotone (fun n => currentPairBoxConnectionEvent n x y) := by
-- proof
  apply StatMech.FrontierB.currentPairBoxConnectionEvent_mono x y

/--
[iUnion_currentPairBoxConnectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma iUnion_currentPairBoxConnectionEvent_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  (⋃ n, currentPairBoxConnectionEvent n x y) = currentPairConnectionEvent x y := by
-- proof
  apply StatMech.FrontierB.iUnion_currentPairBoxConnectionEvent x y

/--
[WeakCurrentConverges.pairBoxConnectionEvent_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma pairBoxConnectionEvent_real_eq
  {d : ℕ}
  {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {m : ℕ}
  {x y : Site d}
-- given
  (hmu : WeakCurrentConverges mu muLim)
  (hnu : WeakCurrentConverges nu nuLim) :
-- imply
  Tendsto (fun k => ((mu k).prod (nu k) : Measure _).real (currentPairBoxConnectionEvent m x y)) atTop (nhds ((muLim.prod nuLim : Measure _).real (currentPairBoxConnectionEvent m x y))) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.pairBoxConnectionEvent_real hmu hnu m x y

/--
[WeakCurrentConverges.pairBoxConnectionEvent_inter_trace_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma pairBoxConnectionEvent_inter_trace_real_eq
  {d : ℕ}
  {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {m : ℕ}
  {x y : Site d}
-- given
  (hmu : WeakCurrentConverges mu muLim)
  (hnu : WeakCurrentConverges nu nuLim)
  (hQ : IsClopen Q) :
-- imply
  Tendsto (fun k => ((mu k).prod (nu k) : Measure _).real (superposedCurrentTrace ⁻¹' (Q ∩ boxConnectionEvent m x y))) atTop (nhds ((muLim.prod nuLim : Measure _).real (superposedCurrentTrace ⁻¹' (Q ∩ boxConnectionEvent m x y)))) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.pairBoxConnectionEvent_inter_trace_real hmu hnu hQ m x y

/--
[currentPairBoxConnectionEvent_measure_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma currentPairBoxConnectionEvent_measure_tendsto_eq
  {d : ℕ}
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {x y : Site d} :
-- imply
  Tendsto (fun n => (mu.prod nu : Measure _) (currentPairBoxConnectionEvent n x y)) atTop (nhds ((mu.prod nu : Measure _) (currentPairConnectionEvent x y))) := by
-- proof
  apply StatMech.FrontierB.currentPairBoxConnectionEvent_measure_tendsto mu nu x y

/--
[currentPairBoxConnectionEvent_inter_measure_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma currentPairBoxConnectionEvent_inter_measure_tendsto_eq
  {d : ℕ}
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {Q : Set (InfiniteCurrentConfig (Sym2 (Site d)) × InfiniteCurrentConfig (Sym2 (Site d)))}
  {x y : Site d} :
-- imply
  Tendsto (fun n => (mu.prod nu : Measure _) (Q ∩ currentPairBoxConnectionEvent n x y)) atTop (nhds ((mu.prod nu : Measure _) (Q ∩ currentPairConnectionEvent x y))) := by
-- proof
  apply StatMech.FrontierB.currentPairBoxConnectionEvent_inter_measure_tendsto mu nu Q x y

/--
[currentPairBoxConnectionEvent_inter_real_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean)
-/
@[path]
private lemma currentPairBoxConnectionEvent_inter_real_tendsto_eq
  {d : ℕ}
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {Q : Set (InfiniteCurrentConfig (Sym2 (Site d)) × InfiniteCurrentConfig (Sym2 (Site d)))}
  {x y : Site d} :
-- imply
  Tendsto (fun n => (mu.prod nu : Measure _).real (Q ∩ currentPairBoxConnectionEvent n x y)) atTop (nhds ((mu.prod nu : Measure _).real (Q ∩ currentPairConnectionEvent x y))) := by
-- proof
  apply StatMech.FrontierB.currentPairBoxConnectionEvent_inter_real_tendsto mu nu Q x y


-- created on 2026-10-23
