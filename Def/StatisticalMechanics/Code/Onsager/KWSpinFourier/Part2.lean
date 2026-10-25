/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier


namespace StatMech.Onsager

noncomputable def ons_KWmatPhase (L : ℕ) (x omega u v : ℂ) :
    Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d2 d1 => ons_dirPhase u v d1.2 * ons_KWmat L x omega d2 d1

noncomputable def ons_KWblockPhase (L : ℕ) (x omega u v : ℂ)
    (g : ZMod L × ZMod L) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun a b => ons_KWmatPhase L x omega u v (g, a) (0, b)

end StatMech.Onsager
