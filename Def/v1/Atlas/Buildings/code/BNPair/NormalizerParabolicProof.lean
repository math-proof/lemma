/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}


namespace NormalizerParabolic

open BNPair

/-- The conjugate Borel $n^{-1} B n = \{n^{-1} b n : b \in B\}$ as a subset of $G$, used to
present $\langle BwB \rangle$ as $\langle B \cup n^{-1}Bn \rangle$. -/
def conjB (bp : BNPair G M) (n : bp.N) : Set G :=
  { g : G | ∃ b ∈ bp.B, g = (n : G)⁻¹ * b * (n : G) }

end NormalizerParabolic
