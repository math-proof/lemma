/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingArfSandwich
import Mathlib.Analysis.SpecificLimits.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich


namespace StatMech.FrontierA

open StatMech.Ising


noncomputable def triangularTorusEvenSubgraphSequence
    (weight : (L : Nat) -> Sym2 (ZMod L × ZMod L) -> Real)
    (n : Nat) : Real := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp [L]; omega⟩
  exact inhomogeneousEvenSubgraphSum (triangularTorusGraph L) (weight L)

noncomputable def triangularTorusSectorSequence
    (weight : (L : Nat) -> Sym2 (ZMod L × ZMod L) -> Real)
    (n : Nat) (a b : Fin 2) : Complex := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp [L]; omega⟩
  exact triangularTorusWeightedSpinCharacterSum L
    (fun edge => (weight L edge : Complex)) a b


end StatMech.FrontierA
