/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose


public section

namespace StatMech.Universality

open Filter Topology Complex HexWalk

open scoped Topology BigOperators


structure HexSideContour (Iτ : Type) (tau : ℕ → ℝ) where
  
  Eτ : HexContourEmb ℕ Iτ
  
  posWit : (∃ v, 1 ≤ v ∧ 0 < tau v) → ∃ i₀ : Iτ, 0 < Eτ.wtContour i₀
  
  shift : Iτ → ℕ → Iτ
  
  shift_inj : ∀ i, Function.Injective (shift i)
  
  shift_wt : ∀ i n, Eτ.wtContour (shift i n) = Eτ.wtContour i


end StatMech.Universality
