/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.InsideClimb.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Onsager.JedBridge.Part2


namespace StatMech.Onsager.JedBridge

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity StatMech.Onsager.InsideClimb

open StatMech.Lattice

open SimpleGraph


def BridgeParityMembership {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) : Prop :=
  ∀ a b : ℤ, rayParity d a b = 1 ↔
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).connectedComponentMk
      ![a, b]).supp.Finite


def BridgeAdjacencyClimb {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) : Prop :=
  ∀ a b : ℤ,
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).Adj ![a, b] ![a + 1, b] ↔
      (∀ k : Fin (m + 3), isVertEdge (d k) → (pos d k).1 = a + 1 →
        ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧
           b < max ((pos d k).2) ((pos d (k + 1)).2)))) ∧
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).Adj ![a, b] ![a, b + 1] ↔
      (∀ k : Fin (m + 3), isHorizEdge (d k) →
        min ((pos d k).1) ((pos d (k + 1)).1) = a → (pos d k).2 ≠ b + 1))

end StatMech.Onsager.JedBridge
