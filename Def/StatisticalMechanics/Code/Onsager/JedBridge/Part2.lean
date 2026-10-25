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
import Theorem.StatisticalMechanics.Code.Onsager.JedBridge


namespace StatMech.Onsager.JedBridge

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity StatMech.Onsager.InsideClimb

open StatMech.Lattice

open SimpleGraph


noncomputable def walkSubgraph {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    PlanarZ2Subgraph where
  V := Fin (m + 3)
  finV := inferInstance
  decV := inferInstance
  G := cycleGraph (m + 3)
  emb := ⟨posSite d, posSite_injective d hsimple⟩
  isSub := walk_isSub d hclosed


end StatMech.Onsager.JedBridge
