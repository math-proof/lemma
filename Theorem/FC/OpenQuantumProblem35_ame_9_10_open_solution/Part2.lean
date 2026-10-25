/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part3
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

@[simp] lemma quinaryWord_zero (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) :
    quinaryWord a v 0 = q5Logical a := rfl

@[simp] lemma quinaryWord_succ (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5)
    (i : Fin 9) : quinaryWord a v (Fin.succ i) = v i := by
  rfl

end OpenQuantumProblem35
