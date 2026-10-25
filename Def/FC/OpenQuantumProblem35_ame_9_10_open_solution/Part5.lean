/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part3
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

def liftPhysicalSet (A : Finset (Fin 9)) : Finset (Fin 10) :=
  {0} ∪ A.map ⟨Fin.succ, Fin.succ_injective 9⟩

end OpenQuantumProblem35
