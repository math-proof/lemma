/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.DLR
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped BigOperators ENNReal

set_option linter.style.longLine false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def isingSpec (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    @Kernel (ConfigSpace (Site d)) (ConfigSpace (Site d)) (outsideSigma (box d n)) _ :=
  @Kernel.mk (ConfigSpace (Site d)) (ConfigSpace (Site d)) (outsideSigma (box d n)) _
    (fun η => fvMeasure η n B β h)
    (@Measure.measurable_of_measurable_coe (ConfigSpace (Site d)) (ConfigSpace (Site d))
      _ (outsideSigma (box d n)) (fun η => fvMeasure η n B β h)
      (fun _ hs => meas_fvMeasure_coe n B β h hs))

end Ising
end StatMech
