/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BlockCirculant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech.Onsager

open scoped Matrix Kronecker

open Matrix


def ons_blockCirculant (n d : ℕ) (v : ZMod n → Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((ZMod n) × Fin d) ((ZMod n) × Fin d) ℂ :=
  fun p q => v (p.1 - q.1) p.2 q.2


noncomputable def ons_blockSymbol (n d : ℕ) [NeZero n] (ω : ℂ)
    (v : ZMod n → Matrix (Fin d) (Fin d) ℂ)
    (j : ZMod n) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ k : ZMod n, ω ^ ((k.val) * (j.val)) • v k

end StatMech.Onsager
