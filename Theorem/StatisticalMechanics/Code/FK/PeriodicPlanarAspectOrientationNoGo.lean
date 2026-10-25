/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
open MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

theorem isFKG_dirac {V : Type} (omega : ConfigSpace (Sym2 V)) :
    IsFKG (Measure.dirac omega) := by
  intro A B hA hB _hAi _hBi
  rw [Measure.real, Measure.real, Measure.real,
    Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hB,
    Measure.dirac_apply' _ (hA.inter hB)]
  by_cases homegaA : omega ∈ A <;>
    by_cases homegaB : omega ∈ B <;>
      simp [homegaA, homegaB]


end StatMech.FK.PeriodicPlanar
