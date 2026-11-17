/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Theorem.StatisticalMechanics.Code.Walls.bc16menger


public section

namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}


structure bc16_DisjointPathFamily (G : SimpleGraph V) (S T : Set V) (ι : Type*) where
  
  a : ι → V
  
  b : ι → V
  
  p : ∀ i, G.Walk (a i) (b i)
  
  ha : ∀ i, a i ∈ S
  
  hb : ∀ i, b i ∈ T
  
  hp : ∀ i, (p i).IsPath
  
  hdisj : ∀ ⦃i j⦄, i ≠ j → ∀ ⦃x⦄, x ∈ (p i).support → x ∉ (p j).support


end StatMech.Walls
