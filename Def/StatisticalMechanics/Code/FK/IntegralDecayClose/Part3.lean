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
import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


noncomputable def idc_cylinderAlg (d : ℕ) : Subalgebra ℝ C(ConfigSpace (Sym2 (Site d)), ℝ) :=
  Algebra.adjoin ℝ (Set.range (idc_coordCM (d := d)))


end FK
end StatMech
