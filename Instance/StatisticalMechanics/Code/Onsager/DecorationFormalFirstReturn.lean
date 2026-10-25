/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part4


namespace StatMech.Onsager

open BigOperators Finset

noncomputable instance ons_decFirstReturnAtom_inhabited
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    Inhabited (ons_DecFirstReturnAtom L d) := by
  let loop : Fin 1 → ons_Dart L := fun _ ↦ d
  refine ⟨⟨0, ⟨loop, ?_, ?_, ?_⟩⟩⟩
  · rfl
  · intro k hk
    exact (hk (Fin.eq_zero k)).elim
  · intro k
    exact (ons_dartRev_ne L d).symm

end StatMech.Onsager
