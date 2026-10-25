/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def triangularSquareHorizontalEdges
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  ((Finset.univ.filter (fun p => triangularTorusEastEdge L p ∈ F)).image
      (fun p => ons_portEdge L (p, 0))) ∆
    ((Finset.univ.filter
      (fun p => triangularTorusNortheastEdge L p ∈ F)).image
        (fun p => ons_portEdge L (p, 0)))

noncomputable def triangularSquareVerticalEdges
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  ((Finset.univ.filter (fun p => triangularTorusNorthEdge L p ∈ F)).image
      (fun p => ons_portEdge L (p, 1))) ∆
    ((Finset.univ.filter
      (fun p => triangularTorusNortheastEdge L p ∈ F)).image
        (fun p => ons_portEdge L ((p.1 + 1, p.2), 1)))


noncomputable def triangularSquareExpansion
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  triangularSquareHorizontalEdges L F ∪ triangularSquareVerticalEdges L F

end StatMech.FrontierA
