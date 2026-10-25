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
import Def.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


@[simp] theorem abigRealParam_some_some (J : Sym2 V -> Real)
    (beta h : Real) (x y : V) :
    abigRealParam J beta h s(some x, some y) = pBeta (J s(x, y)) beta :=
  rfl

@[simp] theorem abigRealParam_some_none (J : Sym2 V -> Real)
    (beta h : Real) (x : V) :
    abigRealParam J beta h s(some x, none) = qField h :=
  rfl


theorem abigRealParam_mem (J : Sym2 V -> Real) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e) :
    forall e, 0 <= abigRealParam J beta h e ∧
      abigRealParam J beta h e <= 1 := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abigRealParam, FieldGhostDict.ghostCoupling]
      · simpa [abigRealParam, FieldGhostDict.ghostCoupling] using qField_mem h hh
      · simpa [abigRealParam, FieldGhostDict.ghostCoupling] using qField_mem h hh
      · constructor
        · simpa [abigRealParam, FieldGhostDict.ghostCoupling] using
            pBeta_nonneg (mul_nonneg hbeta (hJ s(x, y)))
        · exact (pBeta_lt_one (J s(x, y)) beta).le


end Sharpness
end StatMech
