/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import sympy.atlas.StatisticalMechanics.Code.Lattice.HypercubicLattice
import sympy.atlas.StatisticalMechanics.Code.Lattice.DartDef
import sympy.atlas.StatisticalMechanics.Code.Lattice.DartNext
import sympy.atlas.StatisticalMechanics.Code.Lattice.ContourLinksExits
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanExteriorClosure
import sympy.atlas.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop
import sympy.atlas.StatisticalMechanics.Code.Lattice.ExteriorConnected
import sympy.atlas.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness
import sympy.atlas.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import sympy.atlas.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import sympy.atlas.StatisticalMechanics.Code.Lattice.ClosedContourSeparation
import sympy.atlas.StatisticalMechanics.Code.Lattice.OrbitWindingWitness
import sympy.atlas.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import sympy.atlas.StatisticalMechanics.Code.Lattice.CornerBalance
import sympy.atlas.StatisticalMechanics.Code.Walls.kc2_core
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_oddrayeqleftRegion
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_downfaceheadout
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_upleftfacecell
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_tailinK
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_farleftcell

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice




















theorem kc3_leftRegion_eq_of_bdEdgeMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
    K = jec_leftRegion (mpl_orbitLoop K a) := by
  rcases pbs_setIdentity_of_bdEdge_match K (jec_leftRegion (mpl_orbitLoop K a)) hmatch with h | h
  · 
    exact h
  · 
    exfalso
    obtain ⟨q, hqfar, hqK⟩ := kc3_exists_farLeft_orbitLoop a hK
    have hqeven : q ∉ jec_leftRegion (mpl_orbitLoop K a) :=
      kc3_farLeft_notMem_leftRegion a hqfar
    rw [h] at hqK
    simp only [Set.mem_compl_iff, not_not] at hqK
    exact hqeven hqK













theorem kc3_downFaceEven_of_leftRegion_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
    kc2_DownFaceEven K a := by
  intro e he hd _hsupp
  have hnotmem : dartFace e ∉ K := kc3_dartFace_down_notMem he hd
  rw [hKeq, jec_mem_leftRegion, not_not] at hnotmem
  exact hnotmem








theorem kc3_upFaceInK_of_leftRegion_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
    kc2_UpFaceInK K a := by
  intro e _he _hd _hsupp hodd
  rw [hKeq, jec_mem_leftRegion]
  exact hodd







theorem kc3_leftFaceInK_of_leftRegion_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
    kc2_LeftFaceInK K a := by
  intro e _he _hd _hsupp hodd
  rw [hKeq, jec_mem_leftRegion]
  exact hodd





theorem kc3_three_of_leftRegion_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
    kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a :=
  ⟨kc3_downFaceEven_of_leftRegion_eq K a hKeq,
   kc3_upFaceInK_of_leftRegion_eq K a hKeq,
   kc3_leftFaceInK_of_leftRegion_eq K a hKeq⟩









theorem kc3_core_of_leftRegion_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
    exc_SupportOddInK K a := by
  intro z _hz hodd
  rw [hKeq, jec_mem_leftRegion]
  exact hodd










theorem kc3_three_of_bdEdgeMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
    kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a :=
  kc3_three_of_leftRegion_eq K a (kc3_leftRegion_eq_of_bdEdgeMatch K hK a hmatch)









theorem kc3_core_of_bdEdgeMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
    exc_SupportOddInK K a :=
  kc3_core_of_leftRegion_eq K a (kc3_leftRegion_eq_of_bdEdgeMatch K hK a hmatch)






theorem kc3_core_of_bdEdgeMatch_via_three (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
    exc_SupportOddInK K a := by
  obtain ⟨hdown, hup, hleft⟩ := kc3_three_of_bdEdgeMatch K hK a hmatch
  exact kc2_supportOddInK_of_three hdown hup hleft















theorem kc3_leftRegion_eq_of_bridge_halves (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a))) :
    K = jec_leftRegion (mpl_orbitLoop K a) :=
  ccs_cluster_eq_leftRegion (mpl_orbitLoop K a) hin hout






theorem kc3_core_of_bridge_halves (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a))) :
    exc_SupportOddInK K a :=
  kc3_core_of_leftRegion_eq K a (kc3_leftRegion_eq_of_bridge_halves K a hin hout)



theorem kc3_three_of_bridge_halves (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a))) :
    kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a :=
  kc3_three_of_leftRegion_eq K a (kc3_leftRegion_eq_of_bridge_halves K a hin hout)


















theorem kc3_interiorSubset_of_bdEdgeMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a))
    (hoff : exc_OffSupportReachesExterior K a) :
    eaw_InteriorSubset K a :=
  exc_interiorSubset_of_reaches_and_support K a hoff (kc3_core_of_bdEdgeMatch K hK a hmatch)




theorem kc3_interiorSubset_of_bridge_halves (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)))
    (hoff : exc_OffSupportReachesExterior K a) :
    eaw_InteriorSubset K a :=
  exc_interiorSubset_of_reaches_and_support K a hoff (kc3_core_of_bridge_halves K a hin hout)















theorem kc3_unitCell_leftRegion_eq :
    unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
  ext z
  rw [jec_mem_leftRegion]
  constructor
  · intro hz
    rw [unitCell, Set.mem_singleton_iff] at hz
    subst hz
    rw [mpl_unitCell_rayCount_eq_one]
    decide
  · intro hodd
    exact eaw_unitCell_interiorSubset z hodd





theorem kc3_unitCell_bdEdgeMatch :
    pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) :=
  pbs_bdEdgeMatch_of_leftRegion_eq _ kc3_unitCell_leftRegion_eq




theorem kc3_unitCell_three :
    kc2_DownFaceEven unitCell ucBase ∧ kc2_UpFaceInK unitCell ucBase ∧
      kc2_LeftFaceInK unitCell ucBase :=
  kc3_three_of_leftRegion_eq unitCell ucBase kc3_unitCell_leftRegion_eq





theorem kc3_unitCell_core : exc_SupportOddInK unitCell ucBase :=
  kc3_core_of_leftRegion_eq unitCell ucBase kc3_unitCell_leftRegion_eq


















theorem kc3_leftRegion_eq_iff_bdEdgeMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    K = jec_leftRegion (mpl_orbitLoop K a) ↔ pww_BdEdgeMatch K (mpl_orbitLoop K a) :=
  ⟨fun h => pbs_bdEdgeMatch_of_leftRegion_eq _ h,
   fun h => kc3_leftRegion_eq_of_bdEdgeMatch K hK a h⟩



















theorem kc3_core_of_bdEdgeMatch_summary (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
    (kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a) ∧
      exc_SupportOddInK K a :=
  ⟨kc3_three_of_bdEdgeMatch K hK a hmatch, kc3_core_of_bdEdgeMatch K hK a hmatch⟩

end Walls

end StatMech
