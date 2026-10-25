/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part4
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem finBackward_eq_some_iff {n : Nat}
    (f : Fin (n + 1)) (k : Fin n) :
    finBackward f = some k ↔ f = k.succ := by
  refine Fin.cases ?_ (fun z => ?_) f
  · simp only [finBackward, Fin.cases_zero]
    constructor
    · intro h
      simp at h
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
  · simp [finBackward]

@[simp] theorem finForward_eq_some_iff {n : Nat}
    (f : Fin (n + 1)) (k : Fin n) :
    finForward f = some k ↔ f = k.castSucc := by
  refine Fin.lastCases ?_ (fun z => ?_) f
  · simp only [finForward, Fin.lastCases_last]
    constructor
    · intro h
      simp at h
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
  · simp [finForward]


end
end StatMech.FrontierA
