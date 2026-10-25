/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part5
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jfc_sq_interior_bounded : jfc_sq_interior.supp.Finite :=
  whb_faceRegion_interior_bounded


theorem jfc_sq_bounded_eq_interior
    (C : {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite}) :
    C = ⟨jfc_sq_interior, jfc_sq_interior_bounded⟩ := by
  classical
  obtain ⟨x, hx⟩ := Quot.exists_rep C.1
  refine Subtype.ext ?_
  by_cases hx0 : x = ![0, 0]
  · rw [← hx, hx0]; rfl
  · exfalso
    have hmk : (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk x = C.1 := hx
    have houter : C.1 = jfc_whb_outerRegion jbc_Pce := by
      rw [← hmk]; exact jfc_sq_reach_outerRegion hx0
    have hinf : C.1.supp.Infinite := houter ▸ jfc_whb_outerRegion_infinite jbc_Pce
    exact hinf C.2


theorem jfc_sq_faithfulRegionCount : whc_faithfulRegionCount jbc_Pce = 1 := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph jbc_Pce)
      (Set.toFinite (imageGraph jbc_Pce).edgeSet)
  unfold whc_faithfulRegionCount
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => (jfc_sq_bounded_eq_interior a).trans (jfc_sq_bounded_eq_interior b).symm⟩, ?_⟩
  exact ⟨⟨jfc_sq_interior, jfc_sq_interior_bounded⟩⟩


theorem jfc_sq_nullity : nullity jbc_Pce.G = 1 := by
  have h : faceCount jbc_Pce.G = 2 := whb_square_faceCount
  rw [faceCount] at h
  omega


theorem jfc_faithfulDiscreteJordan_unitSquare : whc_FaithfulDiscreteJordan jbc_Pce := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph jbc_Pce)
      (Set.toFinite (imageGraph jbc_Pce).edgeSet)
  have heq : whc_faithfulRegionCount jbc_Pce = nullity jbc_Pce.G := by
    rw [jfc_sq_faithfulRegionCount, jfc_sq_nullity]
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩


theorem jfc_summary :
    whc_FaithfulDiscreteJordan jbc_Pce ∧
      (jfc_EvenDegreeThreading → jeb_FaithfulCountResidue) :=
  ⟨jfc_faithfulDiscreteJordan_unitSquare, jfc_faithfulCountResidue_of_threading⟩

end Lattice
end StatMech
