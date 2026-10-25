/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part5
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

def splitOnEquiv {ι R : Type*} [DecidableEq ι] (A : Finset ι) :
    ((A → R) × ({i : ι // i ∉ A} → R)) ≃ (ι → R) where
  toFun p := pasteOn A p.1 p.2
  invFun f := (fun i => f i.1, fun i => f i.1)
  left_inv p := by
    apply Prod.ext <;> funext i
    · exact pasteOn_mem A p.1 p.2 i
    · exact pasteOn_not_mem A p.1 p.2 i
  right_inv f := by
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, hi]

def permFirstSet (π : Equiv.Perm (Fin 9)) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => (π i).1 < 4)

end OpenQuantumProblem35
