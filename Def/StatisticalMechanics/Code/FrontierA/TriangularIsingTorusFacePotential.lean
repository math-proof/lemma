/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def triangularTorusEastEdge (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) : Sym2 (ZMod L × ZMod L) :=
  (triangularTorusDartEquiv L (p, 1)).edge

noncomputable def triangularTorusNorthEdge (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) : Sym2 (ZMod L × ZMod L) :=
  (triangularTorusDartEquiv L (p, 3)).edge

noncomputable def triangularTorusNortheastEdge (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) : Sym2 (ZMod L × ZMod L) :=
  (triangularTorusDartEquiv L (p, 5)).edge

def triangularTorusPositiveDirection : Fin 3 → Fin 6 := ![1, 3, 5]

end StatMech.FrontierA
