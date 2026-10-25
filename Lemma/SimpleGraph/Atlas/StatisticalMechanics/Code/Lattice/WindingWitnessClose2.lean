import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitnessClose2.Part3
open Finset Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wwc2_odd_iff_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_odd_iff_mem_leftRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  ¬ Even (jec_rayCount z Vc) ↔ z ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.wwc2_odd_iff_mem_leftRegion Vc z

/--
[wwc2_odd_of_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_odd_of_mem_leftRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∈ jec_leftRegion Vc) :
-- imply
  ¬ Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Lattice.wwc2_odd_of_mem_leftRegion Vc hz

/--
[wwc2_far_not_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_far_not_mem_leftRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {q : Site 2}
-- given
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1) :
-- imply
  q ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.wwc2_far_not_mem_leftRegion Vc hq

/--
[wwc2_even_of_connected_to_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_even_of_connected_to_far_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z q : Site 2}
  {p : (hypercubicLattice 2).Walk z q}
-- given
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Lattice.wwc2_even_of_connected_to_far Vc hq p hp

/--
[wwc2_cycle_enclosesCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_cycle_enclosesCell_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hcyc : Vc.IsCycle) :
-- imply
  ∃ z : Site 2, z ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.wwc2_cycle_enclosesCell Vc hcyc

/--
[wwc2_leftRegion_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_leftRegion_nonempty_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hcyc : Vc.IsCycle) :
-- imply
  (jec_leftRegion Vc).Nonempty := by
-- proof
  apply StatMech.Lattice.wwc2_leftRegion_nonempty Vc hcyc

/--
[wwc2_leftRegion_nonempty_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_leftRegion_nonempty_finite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hcyc : Vc.IsCycle)
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  (jec_leftRegion Vc).Nonempty ∧ (jec_leftRegion Vc).Finite := by
-- proof
  apply StatMech.Lattice.wwc2_leftRegion_nonempty_finite Vc hcyc R hsupp

/--
[wwc2_oddOrigin_of_originInside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_oddOrigin_of_originInside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : wwc2_OriginInside ω hfin) :
-- imply
  ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) := by
-- proof
  apply StatMech.Lattice.wwc2_oddOrigin_of_originInside hfin h

/--
[wwc2_exitDartWinds_of_turning_originInside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_exitDartWinds_of_turning_originInside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hinside : wwc2_OriginInside ω hfin) :
-- imply
  acc_ExitDartWinds ω hfin := by
-- proof
  apply StatMech.Lattice.wwc2_exitDartWinds_of_turning_originInside hfin hturn hnp hinside

/--
[wwc2_exitDartWinds_of_cycle_originInside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_exitDartWinds_of_cycle_originInside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hinside : wwc2_OriginInside ω hfin) :
-- imply
  acc_ExitDartWinds ω hfin := by
-- proof
  apply StatMech.Lattice.wwc2_exitDartWinds_of_cycle_originInside hfin hp hnp hinside

/--
[wwc2_anchoredCycleExists_of_turning_originInside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_anchoredCycleExists_of_turning_originInside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hinside : wwc2_OriginInside ω hfin) :
-- imply
  AnchoredCycleExists ω hfin := by
-- proof
  apply StatMech.Lattice.wwc2_anchoredCycleExists_of_turning_originInside hfin hturn hnp hinside

/--
[wwc2_pc_lt_one_of_turning_originInside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_pc_lt_one_of_turning_originInside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧ OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧ wwc2_OriginInside ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.wwc2_pc_lt_one_of_turning_originInside h

/--
[wwc2_unitCell_originInside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_unitCell_originInside_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  origin 2 ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Lattice.wwc2_unitCell_originInside

/--
[wwc2_unitCell_oddOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_unitCell_oddOrigin_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Lattice.wwc2_unitCell_oddOrigin

/--
[wwc2_unitCell_primalLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_unitCell_primalLoop_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (mpl_orbitLoop unitCell ucBase).IsCycle := by
-- proof
  apply StatMech.Lattice.wwc2_unitCell_primalLoop_isCycle

/--
[wwc2_unitCell_enclosesCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_unitCell_enclosesCell_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (jec_leftRegion (mpl_orbitLoop unitCell ucBase)).Nonempty := by
-- proof
  apply StatMech.Lattice.wwc2_unitCell_enclosesCell

/--
[wwc2_exitLoop_isCycle_of_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_exitLoop_isCycle_of_turning_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
-- imply
  (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle := by
-- proof
  apply StatMech.Lattice.wwc2_exitLoop_isCycle_of_turning hfin hturn hnp

/--
[wwc2_turning_enclosesCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_turning_enclosesCell_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
-- imply
  ∃ z₀ : Site 2, z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) := by
-- proof
  apply StatMech.Lattice.wwc2_turning_enclosesCell hfin hturn hnp

/--
[wwc2_originInside_of_reaches_enclosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_originInside_of_reaches_enclosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hreach : ∀ z₀ : Site 2, z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) → ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
-- imply
  wwc2_OriginInside ω hfin := by
-- proof
  apply StatMech.Lattice.wwc2_originInside_of_reaches_enclosed hfin hturn hnp hreach

/--
[wwc2_exitDartWinds_of_turning_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_exitDartWinds_of_turning_reaches_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hreach : ∀ z₀ : Site 2, z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) → ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
-- imply
  acc_ExitDartWinds ω hfin := by
-- proof
  apply StatMech.Lattice.wwc2_exitDartWinds_of_turning_reaches hfin hturn hnp hreach

/--
[wwc2_exitDartWinds_of_originReachesEnclosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_exitDartWinds_of_originReachesEnclosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hreach : wwc2_OriginReachesEnclosed ω hfin) :
-- imply
  acc_ExitDartWinds ω hfin := by
-- proof
  apply StatMech.Lattice.wwc2_exitDartWinds_of_originReachesEnclosed hfin hturn hnp hreach

/--
[wwc2_anchoredCycleExists_of_originReachesEnclosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_anchoredCycleExists_of_originReachesEnclosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
  (hreach : wwc2_OriginReachesEnclosed ω hfin) :
-- imply
  AnchoredCycleExists ω hfin := by
-- proof
  apply StatMech.Lattice.wwc2_anchoredCycleExists_of_originReachesEnclosed hfin hturn hnp hreach

/--
[wwc2_pc_lt_one_of_originReachesEnclosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_pc_lt_one_of_originReachesEnclosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧ OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧ wwc2_OriginReachesEnclosed ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.wwc2_pc_lt_one_of_originReachesEnclosed h

/--
[wwc2_origin_reaches_self_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_origin_reaches_self_offSupport_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hO : origin 2 ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk (origin 2) (origin 2), (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support) := by
-- proof
  apply StatMech.Lattice.wwc2_origin_reaches_self_offSupport hfin hO

/--
[wwc2_unitCell_originReachesEnclosed_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean)
-/
@[path]
private lemma wwc2_unitCell_originReachesEnclosed_witness_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ∃ z₀ : Site 2, z₀ ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) ∧ ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨ z₀ = origin 2 := by
-- proof
  apply StatMech.Lattice.wwc2_unitCell_originReachesEnclosed_witness


-- created on 2026-10-23
