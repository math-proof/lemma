/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
open Finset SimpleGraph
open scoped BigOperators Classical

set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

open Ising

open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def vertexGhostCoupling (J : Sym2 V → ℝ) (H : V → ℝ)
    (e : Sym2 (Option V)) : ℝ :=
  Sym2.lift ⟨fun a b ↦
    match a, b with
    | some x, some y => J s(x, y)
    | some x, none => H x
    | none, some y => H y
    | none, none => 0,
    by rintro (_ | x) (_ | y) <;> simp only [] <;> rw [Sym2.eq_swap]⟩ e

end Sharpness
end StatMech
