/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGauge
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Mathlib.Algebra.Ring.GeomSum
import Def.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


theorem kw_one_sub_internalGadget
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ) :
    1 - kwInternalGadgetTransition external enter exit internal =
      Matrix.fromBlocks (1 - external) (-enter) (-exit) (1 - internal) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [kwInternalGadgetTransition, Matrix.one_apply]


theorem kw_det_eliminateAcyclicInternal
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ)
    (nilpotenceIndex : ℕ) (hpow : internal ^ nilpotenceIndex = 0) :
    (1 - kwInternalGadgetTransition external enter exit internal).det =
      (1 - kwEliminateAcyclicInternal external enter exit internal
        nilpotenceIndex).det := by
  let resolvent := kwNilpotentResolvent internal nilpotenceIndex
  letI : Invertible (1 - internal) :=
    ⟨resolvent,
      kwNilpotentResolvent_mul internal nilpotenceIndex hpow,
      kw_mul_nilpotentResolvent internal nilpotenceIndex hpow⟩
  rw [kw_one_sub_internalGadget, Matrix.det_fromBlocks₂₂]
  have hdetInternal : (1 - internal).det = 1 :=
    det_one_sub_eq_one_of_isNilpotent internal ⟨nilpotenceIndex, hpow⟩
  rw [hdetInternal, one_mul]
  have hinv : ⅟(1 - internal) = resolvent := rfl
  rw [hinv]
  congr 1
  unfold kwEliminateAcyclicInternal
  change (1 - external) - (-enter) * resolvent * (-exit) =
    1 - (external + enter *
      kwNilpotentResolvent internal nilpotenceIndex * exit)
  change (1 - external) - (-enter) * resolvent * (-exit) =
    1 - (external + enter * resolvent * exit)
  simp
  noncomm_ring

end StatMech.FrontierA
