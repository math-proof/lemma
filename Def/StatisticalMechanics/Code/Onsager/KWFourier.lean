/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix
public import Theorem.StatisticalMechanics.Code.Onsager.BlockCirculant2D
public import Theorem.StatisticalMechanics.Code.Onsager.SymbolDet

@[expose] public section

namespace StatMech.Onsager

noncomputable def ons_KWblock (L : ℕ) (x ωt : ℂ) (g : ZMod L × ZMod L) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun a b => ons_KWmat L x ωt (g, a) (0, b)

end StatMech.Onsager
