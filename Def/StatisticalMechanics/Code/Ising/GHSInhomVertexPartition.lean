/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def ghsiGhostCoupling (K : Sym2 V → ℝ) (hf : V → ℝ)
    (e : Sym2 (Option V)) : ℝ :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | some x, some y => 2 * K s(x, y)
    | some x, none => 2 * hf x
    | none, some y => 2 * hf y
    | none, none => 0,
    by rintro (_ | x) (_ | y) <;> simp only [] <;> rw [Sym2.eq_swap]⟩ e

end StatMech.Ising
