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
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


noncomputable def gridEmbed (n : ℕ) (z : Site 2) : Fin 2 → ℝ :=
  fun i => (z i : ℝ) / n


noncomputable def gridFloor (n : ℕ) (p : Fin 2 → ℝ) : Site 2 :=
  fun i => ⌊(n : ℝ) * p i⌋

end ContinuousRectangleCrossing
end StatMech
