/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalCoveragePairScore
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b : ↑m -> Fin 4) : Nat :=
  #(rowClass m a 0 ∆ rowClass m b 0) * (#m + 1) +
    #(canonicalTransferUnion ends m k zero a ∆
      canonicalTransferUnion ends m k zero b)

end StatMech.GrahamGHS.FourColor
