/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


noncomputable def cdc_monomialCM (s : Finset (Sym2 (Site d))) :
    C(ConfigSpace (Sym2 (Site d)), ℝ) :=
  ∏ e ∈ s, idc_coordCM e


noncomputable def cdc_monomialBcf (s : Finset (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact (cdc_monomialCM s)

end FK
end StatMech
