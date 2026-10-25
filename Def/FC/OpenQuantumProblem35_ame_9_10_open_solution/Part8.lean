/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part6
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

def permFrontEquiv (π : Equiv.Perm (Fin 9)) : permFirstSet π ≃ Fin 4 where
  toFun i := ⟨(π i.1).1, (permFirstSet_mem π i.1).mp i.2⟩
  invFun k := ⟨π.symm ⟨k.1, by omega⟩, by simp⟩
  left_inv i := by ext; simp
  right_inv k := by ext; simp

def permRestEquiv (π : Equiv.Perm (Fin 9)) :
    {i : Fin 9 // i ∉ permFirstSet π} ≃ Fin 5 where
  toFun i := ⟨(π i.1).1 - 4, by
    have hn : ¬ (π i.1).1 < 4 := by simpa [permFirstSet] using i.2
    have hu : (π i.1).1 < 9 := (π i.1).2
    omega⟩
  invFun k := ⟨π.symm ⟨k.1 + 4, by omega⟩, by
    simp only [permFirstSet_mem, Equiv.apply_symm_apply]
    omega⟩
  left_inv i := by
    apply Subtype.ext
    apply π.injective
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    have hn : ¬ (π i.1).1 < 4 := by simpa [permFirstSet] using i.2
    omega
  right_inv k := by
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    omega

end OpenQuantumProblem35
