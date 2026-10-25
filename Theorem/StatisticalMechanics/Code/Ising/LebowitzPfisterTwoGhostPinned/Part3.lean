/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned.Part3
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


@[simp] theorem lpTwoGhostCoupling_base
    (J : Sym2 W -> Real) (h : W -> Real) (side : W -> Bool)
    (x y : W) :
    lpTwoGhostCoupling J h side s(Sum.inl x, Sum.inl y) = J s(x, y) := rfl

@[simp] theorem lpTwoGhostCoupling_star
    (J : Sym2 W -> Real) (h : W -> Real) (side : W -> Bool)
    (x : W) :
    lpTwoGhostCoupling J h side
        s(Sum.inl x, Sum.inr (side x)) = h x := by
  simp [lpTwoGhostCoupling]

theorem lpTwoGhostCoupling_nonneg
    (J : Sym2 W -> Real) (h : W -> Real) (side : W -> Bool)
    (hJ : forall e, 0 <= J e) (hh : forall x, 0 <= h x) :
    forall e, 0 <= lpTwoGhostCoupling J h side e := by
  intro e
  induction e with
  | h a b =>
      rcases a with x | g <;> rcases b with y | k
      · exact hJ _
      · change 0 <= if side x = k then h x else 0
        split <;> simp [hh]
      · change 0 <= if side y = g then h y else 0
        split <;> simp [hh]
      · simp [lpTwoGhostCoupling]


end
end StatMech.Ising
