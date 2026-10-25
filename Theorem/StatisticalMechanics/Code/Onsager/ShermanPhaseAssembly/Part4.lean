/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLemma5
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Def.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly.Part4


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_addDartPair_rev_closed (L : ℕ)
    (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e d : ons_Dart L) :
    ons_dartRev L d ∈ ons_addDartPair L forbidden e ↔
      d ∈ ons_addDartPair L forbidden e := by
  have h1 : ons_dartRev L d = e ↔ d = ons_dartRev L e := by
    constructor
    · intro h
      calc
        d = ons_dartRev L (ons_dartRev L d) :=
          (ons_dartRev_involutive L d).symm
        _ = ons_dartRev L e := congrArg (ons_dartRev L) h
    · rintro rfl
      exact ons_dartRev_involutive L e
  have h2 : ons_dartRev L d = ons_dartRev L e ↔ d = e := by
    constructor
    · intro h
      exact (ons_dartRev_involutive L).injective h
    · exact congrArg (ons_dartRev L)
  simp only [ons_addDartPair, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  rw [h1, h2, hforbidden d]
  tauto

end StatMech.Onsager
