/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part11
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalTranslatedRowRootComponentCut
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) : Prop :=
  let K := canonicalTranslatedRow ends m k zero r c
  (StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
      edgeComponent ends K zero = edgeComponent ends K k) ∨
    (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧
      edgeComponent ends (m \ K) zero = edgeComponent ends (m \ K) k)

end StatMech.GrahamGHS.FourColor
