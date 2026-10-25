/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part6
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable def kwg_componentBoundaryGraph (P : PlanarZ2Subgraph) (C : kwg_Face P) :
    SimpleGraph P.V where
  Adj x y := P.G.Adj x y ∧
    Sym2.map P.emb s(x, y) ∈
      jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)
  symm := by
    constructor
    rintro x y ⟨hxy, hmem⟩
    refine ⟨hxy.symm, ?_⟩
    rwa [Sym2.eq_swap]
  loopless := ⟨fun x h => P.G.irrefl h.1⟩

end Ising
end StatMech
