module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part6
public import Def.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part3
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


@[simp] theorem phb_mem_boundarySupport_iff (K : Set (Site 2)) (hK : K.Finite) (f : Site 2) :
    f ∈ phb_boundarySupport K hK ↔ f ∈ (faceBoundaryGraph K).support := by
  simp [phb_boundarySupport]


end Lattice
end StatMech
