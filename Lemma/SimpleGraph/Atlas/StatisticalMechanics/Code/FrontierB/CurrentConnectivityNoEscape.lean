import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape.Part3
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[mem_traceBoundaryConnectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma mem_traceBoundaryConnectionEvent_eq
  {d : ℕ}
  {m : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ traceBoundaryConnectionEvent m x ↔ connBdry d m ω x := by
-- proof
  apply StatMech.FrontierB.mem_traceBoundaryConnectionEvent

/--
[isClopen_traceBoundaryConnectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma isClopen_traceBoundaryConnectionEvent_eq
  {d : ℕ}
  {m : ℕ}
  {x : Site d} :
-- imply
  IsClopen (traceBoundaryConnectionEvent m x) := by
-- proof
  apply StatMech.FrontierB.isClopen_traceBoundaryConnectionEvent m x

/--
[mem_twoArmDisconnectedTraceEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma mem_twoArmDisconnectedTraceEvent_eq
  {d : ℕ}
  {m : ℕ}
  {x y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ twoArmDisconnectedTraceEvent m x y ↔ connBdry d m ω x ∧ connBdry d m ω y ∧ ω ∉ boxConnectionEvent m x y := by
-- proof
  apply StatMech.FrontierB.mem_twoArmDisconnectedTraceEvent

/--
[isClopen_twoArmDisconnectedTraceEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma isClopen_twoArmDisconnectedTraceEvent_eq
  {d : ℕ}
  {m : ℕ}
  {x y : Site d} :
-- imply
  IsClopen (twoArmDisconnectedTraceEvent m x y) := by
-- proof
  apply StatMech.FrontierB.isClopen_twoArmDisconnectedTraceEvent m x y

/--
[mem_traceBoundaryConnectionEvent_of_connected_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma mem_traceBoundaryConnectionEvent_of_connected_outside_eq
  {d : ℕ}
  {m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x z : Site d}
-- given
  (hm : 1 ≤ m)
  (hx : x ∈ box d (m - 1))
  (hz : z ∉ box d (m - 1))
  (hconn : Connected d ω x z) :
-- imply
  ω ∈ traceBoundaryConnectionEvent m x := by
-- proof
  apply StatMech.FrontierB.mem_traceBoundaryConnectionEvent_of_connected_outside hm hx hz hconn

/--
[currentPairTraceBoxGate_diff_subset_twoArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma currentPairTraceBoxGate_diff_subset_twoArm_eq
  {d : ℕ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {m k : ℕ}
  {x y : Site d}
-- given
  (hm : 1 ≤ m)
  (hx : x ∈ box d (m - 1))
  (hy : y ∈ box d (m - 1))
  (_hmk : m ≤ k) :
-- imply
  currentPairTraceBoxGate Q k x y \ currentPairTraceBoxGate Q m x y ⊆ superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent m x y := by
-- proof
  apply StatMech.FrontierB.currentPairTraceBoxGate_diff_subset_twoArm hm hx hy _hmk

/--
[twoArmDisconnectedTraceEvent_antitone_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma twoArmDisconnectedTraceEvent_antitone_of_mem_eq
  {d : ℕ}
  {m n : ℕ}
  {x y : Site d}
-- given
  (hm : 1 ≤ m)
  (hx : x ∈ box d (m - 1))
  (hy : y ∈ box d (m - 1))
  (hmn : m ≤ n) :
-- imply
  twoArmDisconnectedTraceEvent n x y ⊆ twoArmDisconnectedTraceEvent m x y := by
-- proof
  apply StatMech.FrontierB.twoArmDisconnectedTraceEvent_antitone_of_mem hm hx hy hmn

/--
[twoArmDisconnectedTraceEvent_tail_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma twoArmDisconnectedTraceEvent_tail_antitone_eq
  {d : ℕ}
  {R : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d R)
  (hy : y ∈ box d R) :
-- imply
  Antitone (fun n => twoArmDisconnectedTraceEvent (R + n + 1) x y) := by
-- proof
  apply StatMech.FrontierB.twoArmDisconnectedTraceEvent_tail_antitone hx hy

/--
[iInter_twoArmDisconnectedTraceEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma iInter_twoArmDisconnectedTraceEvent_eq
  {d : ℕ}
  {R : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d R)
  (hy : y ∈ box d R) :
-- imply
  (⋂ n, twoArmDisconnectedTraceEvent (R + n + 1) x y) = distinctInfiniteClusterEvent x y := by
-- proof
  apply StatMech.FrontierB.iInter_twoArmDisconnectedTraceEvent hx hy

/--
[distinctInfiniteClusterEvent_subset_atLeastTwoInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma distinctInfiniteClusterEvent_subset_atLeastTwoInfinite_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  distinctInfiniteClusterEvent x y ⊆ atLeastTwoInfinite d := by
-- proof
  apply StatMech.FrontierB.distinctInfiniteClusterEvent_subset_atLeastTwoInfinite x y

/--
[WeakCurrentConverges.pairTraceClopen_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma pairTraceClopen_real_eq
  {d : ℕ}
  {μ ν : ℕ → ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {μLim νLim : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hμ : WeakCurrentConverges μ μLim)
  (hν : WeakCurrentConverges ν νLim)
  (hA : IsClopen A) :
-- imply
  Tendsto (fun k => ((μ k).prod (ν k) : Measure _).real (superposedCurrentTrace ⁻¹' A)) atTop (nhds ((μLim.prod νLim : Measure _).real (superposedCurrentTrace ⁻¹' A))) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.pairTraceClopen_real hμ hν hA

/--
[currentPairConnectivityNoEscape_of_uniqueInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean)
-/
@[path]
private lemma currentPairConnectivityNoEscape_of_uniqueInfiniteCluster_eq
  {d : ℕ}
  {μ ν : ℕ → ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {μLim νLim : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hμ : WeakCurrentConverges μ μLim)
  (hν : WeakCurrentConverges ν νLim)
  (hunique : (independentSuperposedTraceLaw μLim νLim : Measure _) (atLeastTwoInfinite d) = 0) :
-- imply
  CurrentPairConnectivityNoEscape μ ν Q x y := by
-- proof
  apply StatMech.FrontierB.currentPairConnectivityNoEscape_of_uniqueInfiniteCluster hμ hν hunique Q x y


-- created on 2026-10-23
