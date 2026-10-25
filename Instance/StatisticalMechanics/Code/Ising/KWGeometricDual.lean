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
import Abbrev.StatisticalMechanics.Code.Ising.KWGeometricDual
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable instance kwg_edgeFinite (P : PlanarZ2Subgraph) : Finite (kwg_Edge P) :=
  Set.toFinite P.G.edgeSet

noncomputable instance kwg_vertexFintype (P : PlanarZ2Subgraph) : Fintype P.V :=
  Fintype.ofFinite P.V

noncomputable instance kwg_adjDecidable (P : PlanarZ2Subgraph) : DecidableRel P.G.Adj :=
  Classical.decRel _


end Ising
end StatMech
