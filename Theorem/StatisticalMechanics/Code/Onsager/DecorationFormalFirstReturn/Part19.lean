/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part20


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decBoundedRootToUnbounded_bijective
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    Function.Bijective (ons_decBoundedRootToUnbounded L d m) := by
  classical
  constructor
  · intro root root' h
    apply Subtype.ext
    apply ons_decForgetBoundedRoot.injective
    exact congrArg Subtype.val h
  · rintro ⟨root, hexponent⟩
    have hlength := ons_decLoopExponent_length_le L root.2.1
    change root.1 + 1 ≤
      ons_finsuppTotalDegree (ons_decRootedAtomExponent root) at hlength
    rw [hexponent] at hlength
    let bounded : ons_DecRootedAtomBounded L d
        (ons_finsuppTotalDegree m) :=
      ⟨⟨root.1, by omega⟩, root.2⟩
    have hbounded : ons_decBoundedRootExponent bounded = m := by
      simpa only [bounded, ons_decBoundedRootExponent,
        ons_decRootedAtomExponent] using hexponent
    refine ⟨⟨bounded, hbounded⟩, ?_⟩
    apply Subtype.ext
    rfl

end StatMech.Onsager
