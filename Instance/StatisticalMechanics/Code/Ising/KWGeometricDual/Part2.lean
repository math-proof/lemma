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
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable instance kwg_faceFinite (P : PlanarZ2Subgraph) : Finite (kwg_Face P) :=
  jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)

noncomputable instance kwg_faceFintype (P : PlanarZ2Subgraph) : Fintype (kwg_Face P) :=
  Fintype.ofFinite (kwg_Face P)

noncomputable instance kwg_faceDecidableEq (P : PlanarZ2Subgraph) : DecidableEq (kwg_Face P) :=
  Classical.decEq _


end Ising
end StatMech
