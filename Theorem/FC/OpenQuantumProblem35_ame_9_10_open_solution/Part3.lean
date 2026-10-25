/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part4
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

@[simp] lemma pasteOn_mem {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) (i : A) :
    pasteOn A x z i.1 = x i := by simp [pasteOn, i.2]

@[simp] lemma pasteOn_not_mem {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) (i : {i : ι // i ∉ A}) :
    pasteOn A x z i.1 = z i := by simp [pasteOn, i.2]

end OpenQuantumProblem35
