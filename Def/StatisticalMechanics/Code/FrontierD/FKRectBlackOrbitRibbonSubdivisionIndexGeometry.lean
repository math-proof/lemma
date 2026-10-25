/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeInjective
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectListFlatMapReplicate


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectFinSigmaSucc {n : ℕ} (scale : Fin n → ℕ)
    (hscale : ∀ i, 0 < scale i)
    (z : Σ i, Fin (scale i)) : Σ i, Fin (scale i) := by
  letI : NeZero n := ⟨by
    intro hn
    subst n
    exact Fin.elim0 z.1⟩
  exact if hr : z.2.val + 1 < scale z.1 then
      ⟨z.1, ⟨z.2.val + 1, hr⟩⟩
    else
      ⟨z.1 + 1, ⟨0, hscale (z.1 + 1)⟩⟩

end
end StatMech.FrontierD
