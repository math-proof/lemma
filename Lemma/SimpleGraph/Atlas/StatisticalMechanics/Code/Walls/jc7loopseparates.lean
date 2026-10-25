import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc7_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopseparates.lean)
-/
@[path]
private lemma jc7_orbit_isCycle_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  jc6_SingleCycle K := by
-- proof
  apply StatMech.Walls.jc7_orbit_isCycle K hK

/--
[jc7_loop_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopseparates.lean)
-/
@[path]
private lemma jc7_loop_localConstancy_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ (olb_orbitLoop K hK e he).support)
  (hv : v ∉ (olb_orbitLoop K hK e he).support) :
-- imply
  (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔ Even (jec_rayCount v (olb_orbitLoop K hK e he))) := by
-- proof
  apply StatMech.Walls.jc7_loop_localConstancy K hK e he hadj hu hv

/--
[jc7_loop_leftRegion_bdEdge_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopseparates.lean)
-/
@[path]
private lemma jc7_loop_leftRegion_bdEdge_support_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
-- imply
  u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Walls.jc7_loop_leftRegion_bdEdge_support K hK e he hadj hbd

/--
[jc7_loopSeparates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopseparates.lean)
-/
@[path]
private lemma jc7_loopSeparates_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  jc7_LoopSeparates K hK e he := by
-- proof
  apply StatMech.Walls.jc7_loopSeparates K hK e he


-- created on 2026-10-23
