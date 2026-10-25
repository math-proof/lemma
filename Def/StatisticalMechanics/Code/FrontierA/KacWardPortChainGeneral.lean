/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


def kwPortChainState {n : ℕ} (b : Fin n → Fin 2) : Fin (n + 1) → Fin 2 :=
  (List.Vector.scanl (fun x bit : Fin 2 ↦ x + bit) (0 : Fin 2)
    (List.Vector.ofFn b)).get


def KWPortChainEven {n : ℕ} (b : Fin n → Fin 2)
    (y : Fin (n + 1) → Fin 2) : Prop :=
  y 0 = 0 ∧
    (∀ i : Fin n, y i.succ = y i.castSucc + b i) ∧
    y (Fin.last n) = 0

end StatMech.FrontierA
