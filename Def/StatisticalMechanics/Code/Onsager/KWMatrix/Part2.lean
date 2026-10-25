/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.StatisticalMechanics.Code.Onsager.KWMatrix.Part2


namespace StatMech.Onsager

noncomputable def ons_turnW (ω : ℂ) (μ ν : Fin 4) : ℂ :=
  if ν = μ then 1
  else if ν = μ + 1 then ω
  else if ν = μ + 2 then 0
  else ω⁻¹


noncomputable def ons_KWmat (L : ℕ) (x ω : ℂ) : Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d₂ d₁ => if d₂.1 = ons_dirStep L d₁.2 d₁.1 then x * ons_turnW ω d₁.2 d₂.2 else 0


def ons_shiftDart (L : ℕ) (t : ZMod L × ZMod L) (d : ons_Dart L) : ons_Dart L :=
  ((d.1.1 + t.1, d.1.2 + t.2), d.2)


end StatMech.Onsager
