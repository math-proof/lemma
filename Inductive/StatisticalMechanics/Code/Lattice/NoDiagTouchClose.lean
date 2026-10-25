/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

inductive ndt_StarHullMem (K : Set (Site 2)) : Site 2 → Prop
  | base {x : Site 2} (h : x ∈ K) : ndt_StarHullMem K x
  | fillBL {f : Site 2} (h00 : ndt_StarHullMem K (npd_P00 f))
      (h11 : ndt_StarHullMem K (npd_P11 f)) : ndt_StarHullMem K (npd_P10 f)
  | fillTL {f : Site 2} (h10 : ndt_StarHullMem K (npd_P10 f))
      (h01 : ndt_StarHullMem K (npd_P01 f)) : ndt_StarHullMem K (npd_P00 f)


end Lattice
end StatMech
