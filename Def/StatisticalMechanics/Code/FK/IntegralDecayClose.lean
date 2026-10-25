/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralShiftDecay.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


noncomputable def idc_coordCM (e : Sym2 (Site d)) : C(ConfigSpace (Sym2 (Site d)), ℝ) :=
  ⟨fun ω => if ω e then (1 : ℝ) else 0,
    (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (ConfigSpace.continuous_eval e)⟩

end FK
end StatMech
