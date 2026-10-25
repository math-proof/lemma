/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.JordanParity
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossingV.Part2


namespace StatMech.Onsager.InteriorCells

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.WalkCrossingV StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


def interiorSet (d : Fin n → Fin 4) : Set (ℤ × ℤ) := {c | rayParity d c.1 c.2 = 1}


noncomputable def yInf (d : Fin n → Fin 4) : ℤ := Finset.univ.inf' Finset.univ_nonempty (fun k => (pos d k).2)


noncomputable def ySup (d : Fin n → Fin 4) : ℤ := Finset.univ.sup' Finset.univ_nonempty (fun k => (pos d k).2)

end StatMech.Onsager.InteriorCells
