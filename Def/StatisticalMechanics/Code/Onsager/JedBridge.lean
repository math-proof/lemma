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


namespace StatMech.Onsager.JedBridge

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity StatMech.Onsager.InsideClimb

open StatMech.Lattice

open SimpleGraph


def posSite {m : ℕ} (d : Fin (m + 3) → Fin 4) (i : Fin (m + 3)) : Site 2 :=
  ![(pos d i).1, (pos d i).2]

end StatMech.Onsager.JedBridge
