/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Def.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part2
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


theorem qField_toNNReal_le_one (h : Real) : (qField h).toNNReal <= 1 := by
  rw [Real.toNNReal_le_one]
  unfold qField
  linarith [Real.exp_pos (-h)]


theorem abigParam_le_one (J : Sym2 V -> Real) (beta h : Real) :
    forall e, abigParam J beta h e <= 1 := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abigParam, abigRealParam, FieldGhostDict.ghostCoupling]
      · simpa [abigParam, abigRealParam, FieldGhostDict.ghostCoupling] using
          qField_toNNReal_le_one h
      · simpa [abigParam, abigRealParam, FieldGhostDict.ghostCoupling] using
          qField_toNNReal_le_one h
      · simpa [abigParam, abigRealParam, FieldGhostDict.ghostCoupling] using
          pBeta_toNNReal_le_one (J s(x, y)) beta

@[simp] theorem abigParam_some_some (J : Sym2 V -> Real)
    (beta h : Real) (x y : V) :
    abigParam J beta h s(some x, some y) =
      (pBeta (J s(x, y)) beta).toNNReal :=
  rfl

@[simp] theorem abigParam_some_none (J : Sym2 V -> Real)
    (beta h : Real) (x : V) :
    abigParam J beta h s(some x, none) = (qField h).toNNReal :=
  rfl


theorem abigParam_invariant (J : Sym2 V -> Real) (beta h : Real)
    (sigma : V ≃ V)
    (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y))
    (e : Sym2 (Option V)) :
    abigParam J beta h (abfsEdgeEquiv sigma e) = abigParam J beta h e := by
  apply congrArg Real.toNNReal
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abigRealParam, FieldGhostDict.ghostCoupling,
          abfsEdgeEquiv_mk]
      · simp [abigRealParam, FieldGhostDict.ghostCoupling,
          abfsEdgeEquiv_mk]
      · simp [abigRealParam, FieldGhostDict.ghostCoupling,
          abfsEdgeEquiv_mk,
          Sym2.eq_swap]
      · simp [abigRealParam, FieldGhostDict.ghostCoupling,
          abfsEdgeEquiv_mk, hJ]


end Sharpness
end StatMech
