/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.PlusStateDLR.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def isingSpecFull (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    Kernel (ConfigSpace (Site d)) (ConfigSpace (Site d)) :=
  Kernel.mk (fun η => fvMeasure η n B β h)
    (Measure.measurable_of_measurable_coe _
      (fun _ hs => (meas_fvMeasure_coe n B β h hs).mono (outsideSigma_le (box d n)) le_rfl))

end Ising
end StatMech
