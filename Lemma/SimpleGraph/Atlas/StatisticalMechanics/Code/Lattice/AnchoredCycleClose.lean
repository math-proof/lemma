import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.AnchoredCycleClose
open Finset Set SimpleGraph Function StatMech StatMech.Lattice


/--
[acc_oddRay_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_oddRay_mem_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {u : Site 2}
  {z : Site 2}
  {c : (hypercubicLattice 2).Walk u u}
-- given
  (hpos : 0 < jec_rayCount z c) :
-- imply
  ∃ f ∈ c.support, f 0 ≤ z 0 - 1 := by
-- proof
  apply StatMech.Lattice.acc_oddRay_mem_support c hpos

/--
[acc_oddRay_mem_support_subgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_oddRay_mem_support_subgraph_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {G : SimpleGraph (Site 2)}
  {u : Site 2}
  {z : Site 2}
  {c : G.Walk u u}
-- given
  (hle : G ≤ hypercubicLattice 2)
  (hpos : 0 < jec_rayCount z (c.mapLe hle)) :
-- imply
  ∃ f ∈ c.support, f 0 ≤ z 0 - 1 := by
-- proof
  apply StatMech.Lattice.acc_oddRay_mem_support_subgraph hle c hpos

/--
[acc_isCycle_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_isCycle_copy_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {G : SimpleGraph V}
  {u u' : V}
  {c : G.Walk u u}
-- given
  (hu : u = u')
  (h : c.IsCycle) :
-- imply
  (c.copy hu hu).IsCycle := by
-- proof
  apply StatMech.Lattice.acc_isCycle_copy c hu h

/--
[acc_exitFaceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_exitFaceLoop_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle) :
-- imply
  (acc_exitFaceLoop (ω := ω) hfin).IsCycle := by
-- proof
  apply StatMech.Lattice.acc_exitFaceLoop_isCycle hfin hcyc

/--
[acc_exitFaceLoop_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_exitFaceLoop_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (acc_exitFaceLoop (ω := ω) hfin).support = (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support := by
-- proof
  apply StatMech.Lattice.acc_exitFaceLoop_support hfin

/--
[acc_rayCount_exitFaceLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_rayCount_exitFaceLoop_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  jec_rayCount z ((acc_exitFaceLoop (ω := ω) hfin).mapLe (faceBoundaryGraph_le _)) = jec_rayCount z (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) := by
-- proof
  apply StatMech.Lattice.acc_rayCount_exitFaceLoop hfin z

/--
[acc_cycleHasLeftFace_of_oddOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_cycleHasLeftFace_of_oddOrigin_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle)
  (hodd : ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)))) :
-- imply
  CycleHasLeftFace ω hfin := by
-- proof
  apply StatMech.Lattice.acc_cycleHasLeftFace_of_oddOrigin hfin hcyc hodd

/--
[acc_anchoredCycleExists_of_oddOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_anchoredCycleExists_of_oddOrigin_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle)
  (hodd : ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)))) :
-- imply
  AnchoredCycleExists ω hfin := by
-- proof
  apply StatMech.Lattice.acc_anchoredCycleExists_of_oddOrigin hfin hcyc hodd

/--
[acc_anchoredCycleExists_of_exitDartWinds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_anchoredCycleExists_of_exitDartWinds_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : acc_ExitDartWinds ω hfin) :
-- imply
  AnchoredCycleExists ω hfin := by
-- proof
  apply StatMech.Lattice.acc_anchoredCycleExists_of_exitDartWinds hfin h

/--
[acc_pcAnchoredEnclosure_of_exitDartWinds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_pcAnchoredEnclosure_of_exitDartWinds_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), acc_ExitDartWinds ω hfin) :
-- imply
  StatMech.Percolation.PcAnchoredEnclosure := by
-- proof
  apply StatMech.Lattice.acc_pcAnchoredEnclosure_of_exitDartWinds h

/--
[acc_pc_lt_one_of_exitDartWinds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_pc_lt_one_of_exitDartWinds_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), acc_ExitDartWinds ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.acc_pc_lt_one_of_exitDartWinds h

/--
[acc_origin_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_origin_mem_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (_hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (origin 2) ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.acc_origin_mem_cluster _hfin

/--
[acc_oddOrigin_of_cycle_interior_intConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_oddOrigin_of_cycle_interior_intConn_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) → ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) → ¬ Even (jec_rayCount z0 (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
-- imply
  ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) := by
-- proof
  apply StatMech.Lattice.acc_oddOrigin_of_cycle_interior_intConn hfin hp hnp hint hIntConn

/--
[acc_exitDartWinds_of_cycle_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_exitDartWinds_of_cycle_interior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) → ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) → ¬ Even (jec_rayCount z0 (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
-- imply
  acc_ExitDartWinds ω hfin := by
-- proof
  apply StatMech.Lattice.acc_exitDartWinds_of_cycle_interior hfin hp hnp hint hIntConn

/--
[acc_period_ge_three_of_fullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_period_ge_three_of_fullRevolution_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
-- imply
  3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.acc_period_ge_three_of_fullRevolution hfin hturn

/--
[acc_exitDartWinds_of_turning_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_exitDartWinds_of_turning_interior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) → ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) → ¬ Even (jec_rayCount z0 (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
-- imply
  acc_ExitDartWinds ω hfin := by
-- proof
  apply StatMech.Lattice.acc_exitDartWinds_of_turning_interior hfin hturn hnp hint hIntConn

/--
[acc_unitCell_faceInj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_unitCell_faceInj_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1)) (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
-- proof
  apply StatMech.Lattice.acc_unitCell_faceInj

/--
[acc_unitCell_faceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_unitCell_faceLoop_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (mpl_orbitFaceLoop unitCell ucBase).IsCycle := by
-- proof
  apply StatMech.Lattice.acc_unitCell_faceLoop_isCycle

/--
[acc_unitCell_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_unitCell_winds_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (mpl_orbitFaceLoop unitCell ucBase).IsCycle ∧ ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Lattice.acc_unitCell_winds

/--
[acc_unitCell_hasLeftSupportFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean)
-/
@[path]
private lemma acc_unitCell_hasLeftSupportFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ∃ f ∈ (mpl_orbitLoop unitCell ucBase).support, f 0 ≤ -1 := by
-- proof
  apply StatMech.Lattice.acc_unitCell_hasLeftSupportFace


-- created on 2026-10-23
