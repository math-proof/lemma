/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part2
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def triangularPositiveEdge
    (L : Nat) [Fact (2 < L)] (a : Fin 3)
    (p : ZMod L × ZMod L) : Sym2 (ZMod L × ZMod L) :=
  (triangularTorusDartEquiv L
    (p, triangularTorusPositiveDirection a)).edge

noncomputable def triangularPositiveEdgeSources
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (a : Fin 3) :
    Finset (ZMod L × ZMod L) :=
  Finset.univ.filter (fun p => triangularPositiveEdge L a p ∈ F)

noncomputable def triangularPositiveEdgeReconstruction
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  Finset.univ.biUnion (fun a : Fin 3 =>
    (triangularPositiveEdgeSources L F a).image
      (triangularPositiveEdge L a))

end StatMech.FrontierA
