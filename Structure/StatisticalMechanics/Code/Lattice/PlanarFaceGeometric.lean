/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric
public section

open SimpleGraph Set


namespace StatMech.Lattice

structure PlanarZ2Subgraph where
  
  V : Type
  
  finV : Finite V
  
  decV : DecidableEq V
  
  G : SimpleGraph V
  
  emb : V ↪ Site 2
  

  isSub : ∀ ⦃x y : V⦄, G.Adj x y → (hypercubicLattice 2).Adj (emb x) (emb y)

end StatMech.Lattice
