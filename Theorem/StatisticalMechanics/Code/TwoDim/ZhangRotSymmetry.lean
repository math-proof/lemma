/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangClose.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.SelfDualDichotomy
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality


theorem zrs_rotConfig_apply (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    kdi_rotConfig ω e = ω (kdi_rotEdgeEquiv.symm e) := by
  rw [kdi_rotConfig, Equiv.piCongrLeft_apply, eq_rec_constant]


theorem zrs_rotConfig_monotone : Monotone (kdi_rotConfig) := by
  intro ω₁ ω₂ hle b
  rw [zrs_rotConfig_apply, zrs_rotConfig_apply]
  exact hle _


theorem zrs_rotPreimage_isIncreasing {A : Set (ConfigSpace (Sym2 (Site 2)))}
    (hA : IsIncreasing A) : IsIncreasing (kdi_rotConfig ⁻¹' A) :=
  IsUpperSet.preimage hA zrs_rotConfig_monotone


theorem zrs_rotPreimage_measurableSet {A : Set (ConfigSpace (Sym2 (Site 2)))}
    (hA : MeasurableSet A) : MeasurableSet (kdi_rotConfig ⁻¹' A) :=
  kdi_measurable_rotConfig hA


theorem zrs_rotPreimage_measureReal {A : Set (ConfigSpace (Sym2 (Site 2)))}
    (hA : MeasurableSet A) :
    halfMeasure.real (kdi_rotConfig ⁻¹' A) = halfMeasure.real A :=
  kdi_rotConfig_measurePreserving.measureReal_preimage hA.nullMeasurableSet


end TwoDim
end StatMech
