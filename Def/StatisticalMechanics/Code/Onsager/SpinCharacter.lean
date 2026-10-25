/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3


namespace StatMech.Onsager

open BigOperators StatMech.Ising

def ons_spinCharacter (a b : Fin 2) (h : Fin 2 × Fin 2) : ℝ :=
  (-1 : ℝ) ^ ((1 + a.val) * h.1.val + (1 + b.val) * h.2.val +
    h.1.val * h.2.val)

def ons_homologyIntersection (h k : Fin 2 × Fin 2) : Fin 2 :=
  h.1 * k.2 + h.2 * k.1

end StatMech.Onsager
