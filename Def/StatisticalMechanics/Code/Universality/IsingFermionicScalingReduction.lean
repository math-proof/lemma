/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicScalingReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicConvergence
open Filter Set Topology


namespace StatMech.Universality

noncomputable def isingFermionicNormalizedInterpolant
    (delta : Nat → Real) (raw : Nat → ℂ → ℂ) : Nat → ℂ → ℂ :=
  fun n z ↦ raw n z / (Real.sqrt (2 * delta n) : ℂ)

end StatMech.Universality
