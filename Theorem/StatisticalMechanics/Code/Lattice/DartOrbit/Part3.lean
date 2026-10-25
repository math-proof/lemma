/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Def.StatisticalMechanics.Code.Lattice.DartOrbit.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem dartSuccGraph_adj_next (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartSuccGraph K).Adj a (dartNextSub K a) := by
  refine ⟨?_, Or.inl rfl⟩
  intro h
  exact dartNextSub_ne_self K a h.symm


end Lattice
end StatMech
