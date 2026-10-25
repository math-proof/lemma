/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned.Part2
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


def lpTwoGhostCoupling
    (J : Sym2 W -> Real) (h : W -> Real) (side : W -> Bool) :
    Sym2 (LPTwoGhostVertex W) -> Real :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | .inl x, .inl y => J s(x, y)
    | .inl x, .inr g => if side x = g then h x else 0
    | .inr g, .inl x => if side x = g then h x else 0
    | .inr _, .inr _ => 0,
    by rintro (_ | g) (_ | k) <;> simp only [] <;> rw [Sym2.eq_swap]⟩

end
end StatMech.Ising
