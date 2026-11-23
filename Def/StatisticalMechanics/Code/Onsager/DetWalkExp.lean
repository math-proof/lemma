/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetWalkExp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.DetLoopExpansion
public import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
public import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop

@[expose] public section

namespace StatMech.Onsager

open BigOperators

noncomputable def ons_detWalkRoot {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) : ℂ :=
  Complex.exp (-(∑' n : ℕ,
    (∑ v : Fin (n + 1) → E,
      ∏ k : Fin (n + 1), Λ (v k) (v (k + 1))) / (n + 1)) / 2)

def ons_maskMatrix {E : Type*} [DecidableEq E]
    (forbidden : Finset E) (Λ : Matrix E E ℂ) : Matrix E E ℂ :=
  fun i j => if i ∈ forbidden ∨ j ∈ forbidden then 0 else Λ i j

end StatMech.Onsager
