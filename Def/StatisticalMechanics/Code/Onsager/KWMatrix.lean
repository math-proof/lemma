/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Abbrev.StatisticalMechanics.Code.Onsager.KWMatrix

@[expose] public section

namespace StatMech.Onsager

def ons_dirStep (L : ℕ) (μ : Fin 4) (s : ZMod L × ZMod L) : ZMod L × ZMod L :=
  match μ with
  | 0 => (s.1 + 1, s.2)
  | 1 => (s.1, s.2 + 1)
  | 2 => (s.1 - 1, s.2)
  | 3 => (s.1, s.2 - 1)


end StatMech.Onsager
