/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


structure bc19_AFan (G : SimpleGraph V) (A S R : Set V) (k : ℕ) where
  
  a : Fin k → V
  
  c : Fin k → V
  
  q : ∀ i, G.Walk (a i) (c i)
  ha : ∀ i, a i ∈ A
  hc : ∀ i, c i ∈ S
  hq : ∀ i, (q i).IsPath
  
  hmeet : ∀ i, ∀ z ∈ (q i).support, z ∈ S → z = c i
  
  hreg : ∀ i, ∀ z ∈ (q i).support, z ∈ R
  
  hdisj : ∀ ⦃i j⦄, i ≠ j → ∀ ⦃z⦄, z ∈ (q i).support → z ∉ (q j).support

end StatMech.Walls
