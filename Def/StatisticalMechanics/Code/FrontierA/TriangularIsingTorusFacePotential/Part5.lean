/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part4
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def triangularZeroHomologyLowerPotential
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  triangularZeroHomologyUpperPotential L F p +
    (ZMod.finEquiv 2)
      (ons_edgeBit F (triangularTorusNortheastEdge L p))

end StatMech.FrontierA
