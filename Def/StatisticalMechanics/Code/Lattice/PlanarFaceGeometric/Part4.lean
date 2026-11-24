module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part3
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Lattice

attribute [instance] PlanarZ2Subgraph.finV PlanarZ2Subgraph.decV


noncomputable def exteriorToRegionHom (P : PlanarZ2Subgraph) (R : ℕ)
    (hR : ∀ v : P.V, P.emb v ∈ box 2 R) :
    ((hypercubicLattice 2).induce (exterior 2 R)) →g (regionGraph (imageGraph P)) where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    exact regionGraph_adj_of_exterior P R hR (mem_box_compl_of_exterior a.2) hab


end StatMech.Lattice
