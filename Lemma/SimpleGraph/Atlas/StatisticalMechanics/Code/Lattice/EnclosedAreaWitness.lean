import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[eaw_no_monotone_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_no_monotone_loop_eq
  {g : ℕ → ℤ}
  {L : ℕ}
-- given
  (h3 : 3 ≤ L)
  (hloop : g 0 = g L)
  (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
  (hne : g 1 ≠ g 0)
  (hinj : Set.InjOn g {i | i ≤ L - 1}) :
-- imply
  False := by
-- proof
  apply StatMech.Lattice.eaw_no_monotone_loop g L h3 hloop hstep hne hinj

/--
[eaw_getVert_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_getVert_edge_mem_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {i : ℕ}
-- given
  (hi : i < Vc.length) :
-- imply
  s(Vc.getVert i, Vc.getVert (i + 1)) ∈ Vc.edges := by
-- proof
  apply StatMech.Lattice.eaw_getVert_edge_mem Vc hi

/--
[eaw_exists_vertEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_exists_vertEdge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hcyc : Vc.IsCycle) :
-- imply
  ∃ i, i < Vc.length ∧ (Vc.getVert i) 0 = (Vc.getVert (i + 1)) 0 := by
-- proof
  apply StatMech.Lattice.eaw_exists_vertEdge Vc hcyc

/--
[eaw_mem_edges_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_mem_edges_exists_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (h : s(x, y) ∈ Vc.edges) :
-- imply
  ∃ i, i < Vc.length ∧ s(Vc.getVert i, Vc.getVert (i + 1)) = s(x, y) := by
-- proof
  apply StatMech.Lattice.eaw_mem_edges_exists Vc h

/--
[eaw_rayCount_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_rayCount_extreme_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c r : ℤ}
-- given
  (hmin : ∀ x y : Site 2, s(x, y) ∈ Vc.edges → x 0 = y 0 → c ≤ x 0)
  (he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ Vc.edges)
  (hnodup : Vc.edges.Nodup) :
-- imply
  jec_rayCount (![c + 1, r + 1] : Site 2) Vc = 1 := by
-- proof
  apply StatMech.Lattice.eaw_rayCount_extreme Vc c r hmin he0 hnodup

/--
[eaw_cycle_oddCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_cycle_oddCell_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hcyc : Vc.IsCycle) :
-- imply
  ∃ z : Site 2, jec_rayCount z Vc = 1 := by
-- proof
  apply StatMech.Lattice.eaw_cycle_oddCell Vc hcyc

/--
[eaw_cycle_oddCell'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_cycle_oddCell'_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hcyc : Vc.IsCycle) :
-- imply
  ∃ z : Site 2, ¬ Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Lattice.eaw_cycle_oddCell' Vc hcyc

/--
[eaw_windingWitness_of_cycle_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_windingWitness_of_cycle_interior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hnp : OrbitFaceNoPinch K a)
  (hint : eaw_InteriorSubset K a) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.eaw_windingWitness_of_cycle_interior K a hp hnp hint

/--
[eaw_windingSaturatingWitness_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_windingSaturatingWitness_of_residue_eq
-- given
  (hres : eaw_LoopWindsRegion) :
-- imply
  wei_WindingSaturatingWitness := by
-- proof
  apply StatMech.Lattice.eaw_windingSaturatingWitness_of_residue hres

/--
[eaw_starHull_windingWitness_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_starHull_windingWitness_of_residue_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hres : eaw_LoopWindsRegion)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  wei_WindingWitness (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.eaw_starHull_windingWitness_of_residue hres K hSK hne a

/--
[eaw_unitCell_rayCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_unitCell_rayCount_eq_eq
  {z : Site 2} :
-- imply
  jec_rayCount z (mpl_orbitLoop unitCell ucBase) = (if 0 ≤ z 0 - 1 ∧ z 1 = 0 then 1 else 0) + (if -1 ≤ z 0 - 1 ∧ z 1 = 0 then 1 else 0) := by
-- proof
  apply StatMech.Lattice.eaw_unitCell_rayCount_eq z

/--
[eaw_unitCell_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_unitCell_interiorSubset_eq :
-- imply
  eaw_InteriorSubset unitCell ucBase := by
-- proof
  apply StatMech.Lattice.eaw_unitCell_interiorSubset

/--
[eaw_unitCell_loopWindsRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_unitCell_loopWindsRegion_eq :
-- imply
  3 ≤ dartOrbitPeriod unitCell ucBase ∧ OrbitFaceNoPinch unitCell ucBase ∧ eaw_InteriorSubset unitCell ucBase := by
-- proof
  apply StatMech.Lattice.eaw_unitCell_loopWindsRegion

/--
[eaw_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean)
-/
@[path]
private lemma eaw_unitCell_windingWitness_eq :
-- imply
  wei_WindingWitness unitCell ucBase := by
-- proof
  apply StatMech.Lattice.eaw_unitCell_windingWitness


-- created on 2026-10-23
