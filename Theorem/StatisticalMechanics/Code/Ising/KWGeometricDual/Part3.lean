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
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part3
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_flanks_adj (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    (hypercubicLattice 2).Adj (kwg_flankLeft P e) (kwg_flankRight P e) :=
  (kwg_exists_flankingFaces P e).choose_spec.choose_spec.1

theorem kwg_flanks_shared (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    sharedPrimalEdge (kwg_flankLeft P e) (kwg_flankRight P e) = kwg_embeddedEdge P e :=
  (kwg_exists_flankingFaces P e).choose_spec.choose_spec.2


end Ising
end StatMech
