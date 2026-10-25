/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part3
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


noncomputable def sampleTime (N k : ℕ) (hk : k ≤ N) (hN : 0 < N) : unitInterval :=
  ⟨(k : ℝ) / N, by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 (by exact_mod_cast hk)⟩

end ContinuousRectangleCrossing
end StatMech
