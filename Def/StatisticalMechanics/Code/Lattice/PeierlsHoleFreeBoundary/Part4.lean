module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part3
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


noncomputable def phb_planarBoundary (K : Set (Site 2)) (hK : K.Finite) :
    PlanarZ2Subgraph where
  V := (faceBoundaryGraph K).support
  finV := (phb_faceBoundaryGraph_support_finite K hK).to_subtype
  decV := Classical.decEq _
  G := (faceBoundaryGraph K).induce (faceBoundaryGraph K).support
  emb := Function.Embedding.subtype _
  isSub := by
    intro x y hxy
    exact faceBoundaryGraph_le K hxy


end Lattice
end StatMech
