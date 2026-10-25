/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEvalAlgebra.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEval


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalBucketTerm
    (L : ℕ) [NeZero L] (omega u v : ℂ) (decWeight : ons_DecEdge L → ℂ)
    (r : ℕ) (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  ((∑ d : Fin (r + 1) → ons_Dart L,
      if ons_decLoopExponent L d = m then
        ons_decLoopScalar L omega u v d
      else 0) / ((r : ℂ) + 1)) *
    m.prod (fun edge n ↦ decWeight edge ^ n)

end StatMech.Onsager
