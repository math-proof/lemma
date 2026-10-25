/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Def.StatisticalMechanics.Code.Lattice.JordanCycleSpace2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcx_whb_total_count_of_evenResidue (P : PlanarZ2Subgraph)
    (hP : jeb_EvenDegreeSubgraph P) (hres : jcx_EvenCountResidue P) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have hcc : jce_ClosedContour (jei_pushGraph P P.G).edgeSet := by
    rw [jei_pushGraph_G P]; exact hP
  have h := hres P.G le_rfl hcc
  rwa [jei_pushGraph_G P] at h


theorem jcx_faithfulRegionCount_eq_nullity_of_evenResidue (P : PlanarZ2Subgraph)
    (hP : jeb_EvenDegreeSubgraph P) (hres : jcx_EvenCountResidue P) :
    whc_faithfulRegionCount P = nullity P.G := by
  have htot := jcx_whb_total_count_of_evenResidue P hP hres
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega


theorem jcx_faithfulDiscreteJordan_of_evenResidue (P : PlanarZ2Subgraph)
    (hP : jeb_EvenDegreeSubgraph P) (hres : jcx_EvenCountResidue P) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jcx_faithfulRegionCount_eq_nullity_of_evenResidue P hP hres
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩


theorem jcx_faithfulCountResidue_of_evenResidue
    (h : ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P → jcx_EvenCountResidue P) :
    jeb_FaithfulCountResidue :=
  fun P hP => jcx_faithfulDiscreteJordan_of_evenResidue P hP (h P hP)


end Lattice
end StatMech
