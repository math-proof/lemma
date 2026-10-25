/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part3
open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


@[simp] theorem torusEdgeCodeEquiv_apply (L : ℕ) [Fact (2 < L)]
    (c : TorusEdgeCode L) :
    torusEdgeCodeEquiv L c = torusEdgeOfCode L c := rfl


end StatMech.BeffaraDC
