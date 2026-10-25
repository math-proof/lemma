/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopClassification


namespace StatMech.Onsager

open Finset SimpleGraph

noncomputable def ons_decLoopExternalExponent
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_DecEdge L →₀ ℕ :=
  ∑ k, Finsupp.single s(d k, ons_dartRev L (d k)) 1

noncomputable def ons_decLoopInternalExponent
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_DecEdge L →₀ ℕ :=
  ∑ k, ∑ i ∈ ons_decChainPathIndices ((d (k + 1)).2 + 2) (d k).2,
    Finsupp.single (ons_decChainEdge (d k).1 i) 1

end StatMech.Onsager
