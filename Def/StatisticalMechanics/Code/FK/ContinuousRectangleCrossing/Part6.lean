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
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part5
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


noncomputable def sampledGrid {p q : Fin 2 → ℝ} (n N : ℕ) (hN : 0 < N)
    (gamma : Path p q) (k : ℕ) : Site 2 :=
  gridFloor n (gamma (sampleTime N (min k N) (min_le_right k N) hN))

end ContinuousRectangleCrossing
end StatMech
