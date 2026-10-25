/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Def.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


namespace HexFiniteStripCoreIncidenceEnumeration

variable {V : Type*} [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing} {C : HexFiniteStripBoundaryCore R h0 D P}


theorem exists_startIncidence (E : HexFiniteStripCoreIncidenceEnumeration C) :
    ∃ eA : HexIncidence V,
      hexFiniteStripPhysicalStartFiber (R := R) P = {eA} := by
  obtain ⟨eA, heA, hmidA⟩ :=
    E.side_complete R.start R.start_mem (Or.inl rfl)
  refine ⟨eA, ?_⟩
  ext e
  simp only [hexFiniteStripPhysicalStartFiber, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨he, hmid⟩
    exact E.boundary_mid_injective e he eA heA (hmid.trans hmidA.symm)
  · rintro rfl
    exact ⟨heA, hmidA⟩

end HexFiniteStripCoreIncidenceEnumeration
end StatMech.Universality
