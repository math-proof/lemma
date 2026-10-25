/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part3
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

section Iso

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


def fsm_sym2Congr (φ : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map φ
  invFun := Sym2.map φ.symm
  left_inv z := by induction z using Sym2.ind with | _ a b => simp [Sym2.map_mk]
  right_inv z := by induction z using Sym2.ind with | _ a b => simp [Sym2.map_mk]


noncomputable def fsm_openSubIso (φ : G ≃g H) (ω : Sym2 W → Bool) :
    openSub G (fun e => ω (Sym2.map φ.toEquiv e)) ≃g openSub H ω where
  toEquiv := φ.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [openSub_adj, Sym2.map_mk]
    exact and_congr φ.map_rel_iff Iff.rfl


end Iso
end FK
end StatMech
