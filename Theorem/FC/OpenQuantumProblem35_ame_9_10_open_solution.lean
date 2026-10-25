/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part2
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

@[simp] lemma localPartsEquiv_apply (x : Fin 10) :
    localPartsEquiv x = (bitPart x, quintPart x) := rfl


end OpenQuantumProblem35
