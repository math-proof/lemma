import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle
open SimpleGraph Function Set Finset StatMech StatMech.Lattice


/--
[usc_dir_mem_fourDirs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_dir_mem_fourDirs_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart} :
-- imply
  e.dir ∈ usc_fourDirs := by
-- proof
  apply StatMech.Lattice.usc_dir_mem_fourDirs e

/--
[usc_fourDirs_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_fourDirs_card_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  usc_fourDirs.card = 4 := by
-- proof
  apply StatMech.Lattice.usc_fourDirs_card

/--
[usc_dir_injOn_of_face_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_dir_injOn_of_face_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {f : Site 2}
  {T : Set Dart}
-- given
  (hT : ∀ e ∈ T, dartFace e = f) :
-- imply
  Set.InjOn (fun e : Dart => e.dir) T := by
-- proof
  apply StatMech.Lattice.usc_dir_injOn_of_face_eq f T hT

/--
[usc_dir_injOn_visitSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_dir_injOn_visitSet_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2} :
-- imply
  Set.InjOn (fun i => ((dartNext K)^[i] a.1).dir) (usc_visitSet K a f) := by
-- proof
  apply StatMech.Lattice.usc_dir_injOn_visitSet K a f

/--
[usc_orbitFace_multiplicity_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_orbitFace_multiplicity_le_four_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2} :
-- imply
  (usc_visitSet K a f).card ≤ 4 := by
-- proof
  apply StatMech.Lattice.usc_orbitFace_multiplicity_le_four K a f

/--
[usc_faceInjOn_iff_visit_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_faceInjOn_iff_visit_le_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) ↔ ∀ f : Site 2, (usc_visitSet K a f).card ≤ 1 := by
-- proof
  apply StatMech.Lattice.usc_faceInjOn_iff_visit_le_one K a

/--
[usc_noPinch_iff_singleVisit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_noPinch_iff_singleVisit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  OrbitFaceNoPinch K a ↔ ∀ f : Site 2, (usc_visitSet K a f).card ≤ 1 := by
-- proof
  apply StatMech.Lattice.usc_noPinch_iff_singleVisit K a

/--
[usc_faceMultiplicityOne_iff_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_faceMultiplicityOne_iff_noPinch_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  usc_FaceMultiplicityOne K a ↔ OrbitFaceNoPinch K a := by
-- proof
  apply StatMech.Lattice.usc_faceMultiplicityOne_iff_noPinch K a

/--
[usc_totalTurnZ_eq_sum_localTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_totalTurnZ_eq_sum_localTurn_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = ∑ f ∈ usc_orbitFaces K a, usc_localTurn K a f := by
-- proof
  apply StatMech.Lattice.usc_totalTurnZ_eq_sum_localTurn K a

/--
[usc_singleVisit_local_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_singleVisit_local_turn_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
  {i : ℕ}
-- given
  (h : usc_visitSet K a f = {i}) :
-- imply
  usc_localTurn K a f = turnZ K ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Lattice.usc_singleVisit_local_turn K a f i h

/--
[usc_abs_localTurn_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_abs_localTurn_le_four_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2} :
-- imply
  |usc_localTurn K a f| ≤ 4 := by
-- proof
  apply StatMech.Lattice.usc_abs_localTurn_le_four K a f

/--
[usc_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_orbit_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hnp : OrbitFaceNoPinch K a) :
-- imply
  ((dartOrbitFaceWalk K a.1 a.2 (dartOrbitPeriod K a)).copy rfl (by rw [orbit_iterate_period_eq K a])).IsCycle := by
-- proof
  apply StatMech.Lattice.usc_orbit_isCycle K a hp hnp

/--
[usc_orbitFaceSimple_of_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_orbitFaceSimple_of_noPinch_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
-- imply
  OrbitFaceSimple ω hfin := by
-- proof
  apply StatMech.Lattice.usc_orbitFaceSimple_of_noPinch hfin hp hnp

/--
[usc_exitMinFaceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_exitMinFaceLoop_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
  (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
-- imply
  (exitMinFaceLoop (ω := ω) hfin).IsCycle := by
-- proof
  apply StatMech.Lattice.usc_exitMinFaceLoop_isCycle hfin hp hnp

/--
[usc_pc_lt_one_of_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_pc_lt_one_of_noPinch_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧ OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧ ExitDartsSameOrbit ω hfin) :
-- imply
  (StatMech.Percolation.pc 2 : ℝ) < 1 := by
-- proof
  apply StatMech.Lattice.usc_pc_lt_one_of_noPinch h

/--
[usc_unitCell_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_unitCell_noPinch_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  OrbitFaceNoPinch unitCell ucBase := by
-- proof
  apply StatMech.Lattice.usc_unitCell_noPinch

/--
[usc_unitCell_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_unitCell_faceMultiplicityOne_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  usc_FaceMultiplicityOne unitCell ucBase := by
-- proof
  apply StatMech.Lattice.usc_unitCell_faceMultiplicityOne

/--
[usc_unitCell_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_unitCell_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ((dartOrbitFaceWalk unitCell ucBase.1 ucBase.2 (dartOrbitPeriod unitCell ucBase)).copy rfl (by rw [orbit_iterate_period_eq unitCell ucBase])).IsCycle := by
-- proof
  apply StatMech.Lattice.usc_unitCell_isCycle

/--
[usc_domino_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_domino_noPinch_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  OrbitFaceNoPinch domino dmBase := by
-- proof
  apply StatMech.Lattice.usc_domino_noPinch

/--
[usc_domino_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_domino_faceMultiplicityOne_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  usc_FaceMultiplicityOne domino dmBase := by
-- proof
  apply StatMech.Lattice.usc_domino_faceMultiplicityOne

/--
[usc_domino_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean)
-/
@[path]
private lemma usc_domino_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ((dartOrbitFaceWalk domino dmBase.1 dmBase.2 (dartOrbitPeriod domino dmBase)).copy rfl (by rw [orbit_iterate_period_eq domino dmBase])).IsCycle := by
-- proof
  apply StatMech.Lattice.usc_domino_isCycle


-- created on 2026-10-23
