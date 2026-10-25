/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BlockCirculant2D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.BlockCirculant


namespace StatMech.Onsager

open scoped Matrix Kronecker

open Matrix


def ons_blockCirculant2D (L d : ℕ) (v : (ZMod L × ZMod L) → Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((ZMod L × ZMod L) × Fin d) ((ZMod L × ZMod L) × Fin d) ℂ :=
  fun p q => v (p.1.1 - q.1.1, p.1.2 - q.1.2) p.2 q.2


noncomputable def ons_blockSymbol2D (L d : ℕ) [NeZero L] (ω : ℂ)
    (v : (ZMod L × ZMod L) → Matrix (Fin d) (Fin d) ℂ) (j : ZMod L × ZMod L) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ k : ZMod L × ZMod L, ω ^ (k.1.val * j.1.val + k.2.val * j.2.val) • v k

end StatMech.Onsager
