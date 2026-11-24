module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace
open SimpleGraph Set List Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

instance jcs_verts_finite {V : Type*} {G : SimpleGraph V} {u w : V} (c : G.Walk u w) :
    Finite ↑c.toSubgraph.verts := by
  rw [c.verts_toSubgraph]; exact (c.support.finite_toSet).to_subtype


end Lattice
end StatMech
