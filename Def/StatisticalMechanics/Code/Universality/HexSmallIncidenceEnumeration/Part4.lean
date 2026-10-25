/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Structure.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


namespace HexFiniteStripFourPhaseLiftData

variable {V : Type*} [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}

variable {O : HexFiniteStripCoreOrientation C} {G : HexRegion}


noncomputable def toFourPhaseData
    (Q : HexFiniteStripFourPhaseLiftData O G) :
    HexFiniteStripFourPhaseData C G where
  start_eq := Q.start_eq
  heading := O.heading
  hgeom := O.hgeom
  startIncidence := O.startIncidence
  startFiber_singleton := by
    rw [← O.startFiber_singleton]
    ext e
    simp only [hexFiniteStripPhysicalStartFiber, Finset.mem_filter]
    constructor
    · rintro ⟨he, hcls⟩
      refine ⟨he, ?_⟩
      have hp := (Q.class_eq e he 0).mp hcls
      simpa [hexFiniteStripCoreContourPart] using hp
    · rintro ⟨he, hmid⟩
      refine ⟨he, (Q.class_eq e he 0).mpr ?_⟩
      simpa [hexFiniteStripCoreContourPart] using hmid
  start_mid := O.start_mid.trans Q.start_eq.symm
  start_heading := O.start_heading
  headL := O.headL
  headTp := O.headTp
  headTm := O.headTm
  headU := O.headU
  hHeadL := by
    intro e he
    obtain ⟨heb, hcls⟩ := Finset.mem_filter.mp he
    apply O.hHeadL e heb
    have hp := (Q.class_eq e heb 1).mp hcls
    simpa [hexFiniteStripCoreContourPart] using hp
  hHeadTp := by
    intro e he
    obtain ⟨heb, hcls⟩ := Finset.mem_filter.mp he
    apply O.hHeadTp e heb
    have hp := (Q.class_eq e heb 2).mp hcls
    simpa [hexFiniteStripCoreContourPart] using hp
  hHeadTm := by
    intro e he
    obtain ⟨heb, hcls⟩ := Finset.mem_filter.mp he
    apply O.hHeadTm e heb
    have hp := (Q.class_eq e heb 3).mp hcls
    simpa [hexFiniteStripCoreContourPart] using hp
  hHeadU := by
    intro e he
    obtain ⟨heb, hcls⟩ := Finset.mem_filter.mp he
    apply O.hHeadU e heb
    have hp := (Q.class_eq e heb 4).mp hcls
    simpa [hexFiniteStripCoreContourPart] using hp
  taup := Q.taup
  taum := Q.taum
  tau_eq := Q.tau_eq
  phaseL := Q.phaseL
  phaseTp := Q.phaseTp
  phaseTm := Q.phaseTm
  phaseU := Q.phaseU

end HexFiniteStripFourPhaseLiftData


def hexSmallCellHeading (h0 : ℤ) (j : Fin 3) : ℤ :=
  h0 + 3 + 2 * (j : ℤ)


end StatMech.Universality
