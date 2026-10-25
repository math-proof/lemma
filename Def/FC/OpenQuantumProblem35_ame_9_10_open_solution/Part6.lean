/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part4
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

def splitFunctionsEquiv (ι : Type*) :
    (ι → Fin 10) ≃ (ι → ZMod 2) × (ι → ZMod 5) where
  toFun z := (fun i => bitPart (z i), fun i => quintPart (z i))
  invFun z := fun i => localPartsEquiv.symm (z.1 i, z.2 i)
  left_inv z := by
    funext i
    exact localPartsEquiv.symm_apply_apply (z i)
  right_inv z := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst (localPartsEquiv.apply_symm_apply (z.1 i, z.2 i))
    · funext i
      exact congrArg Prod.snd (localPartsEquiv.apply_symm_apply (z.1 i, z.2 i))

end OpenQuantumProblem35
