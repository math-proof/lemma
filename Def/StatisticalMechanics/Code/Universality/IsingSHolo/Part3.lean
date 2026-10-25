/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part2


namespace StatMech.Universality

open Complex


def IsSHolomorphic {ι : Type*} (f : ℂ → ℂ) (edges : ι → ℂ × ℂ × ℂ) : Prop :=
  ∀ i, isingProj (edges i).1 (f (edges i).2.1) = isingProj (edges i).1 (f (edges i).2.2)


noncomputable def isingF : Fin 4 → ℂ → ℂ
  | 0 => fun X => X + X / (Real.sqrt 2 : ℂ)
  | 1 => fun X => isingLambda ^ 2 * X / (Real.sqrt 2 : ℂ)
  | 2 => fun X => isingLambda⁻¹ * X / (Real.sqrt 2 : ℂ)
  | 3 => fun X => isingLambda * X + isingLambda * X / (Real.sqrt 2 : ℂ)


end StatMech.Universality
