/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part6
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

@[simp] lemma bitPart_localPartsEquiv_symm (u : ZMod 2) (v : ZMod 5) :
    bitPart (localPartsEquiv.symm (u, v)) = u := by
  exact congrArg Prod.fst (localPartsEquiv.apply_symm_apply (u, v))

@[simp] lemma quintPart_localPartsEquiv_symm (u : ZMod 2) (v : ZMod 5) :
    quintPart (localPartsEquiv.symm (u, v)) = v := by
  exact congrArg Prod.snd (localPartsEquiv.apply_symm_apply (u, v))

end OpenQuantumProblem35
