/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2


namespace StatMech.Onsager

noncomputable def ons_dirPhase (u v : ℂ) (mu : Fin 4) : ℂ :=
  match mu with
  | 0 => u
  | 1 => v
  | 2 => u⁻¹
  | 3 => v⁻¹

def ons_dirExponentX (mu : Fin 4) : ℤ :=
  match mu with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | 3 => 0

def ons_dirExponentY (mu : Fin 4) : ℤ :=
  match mu with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => -1

end StatMech.Onsager
