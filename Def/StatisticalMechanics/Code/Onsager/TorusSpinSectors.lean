/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CoeffMatch
import Theorem.StatisticalMechanics.Code.Onsager.Torus


namespace StatMech.Onsager

open StatMech.Ising


def ons_xSeamEdge (L : ℕ) (e : Sym2 (ZMod L × ZMod L)) : Prop :=
  ∃ y : ZMod L, e = s(((0 : ZMod L), y), (-1, y))


def ons_ySeamEdge (L : ℕ) (e : Sym2 (ZMod L × ZMod L)) : Prop :=
  ∃ x : ZMod L, e = s((x, (0 : ZMod L)), (x, -1))

noncomputable def ons_evenHomology (L : ℕ)
    (F : Finset (Sym2 (ZMod L × ZMod L))) : Fin 2 × Fin 2 :=
  by
    classical
    exact (⟨(F.filter (ons_xSeamEdge L)).card % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨(F.filter (ons_ySeamEdge L)).card % 2, Nat.mod_lt _ (by decide)⟩)

end StatMech.Onsager
