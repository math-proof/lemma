/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part17


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decBoundedTupleToUnbounded_bijective
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    Function.Bijective (ons_decBoundedTupleToUnbounded L d m) := by
  classical
  constructor
  · intro atoms atoms' h
    apply Subtype.ext
    funext i
    apply ons_decForgetBoundedAtom.injective
    exact congrFun (congrArg Subtype.val h) i
  · rintro ⟨atoms, hexponent⟩
    have hbound : ∀ i,
        (atoms i).1 + 1 ≤ ons_finsuppTotalDegree m := by
      intro i
      have hcomponent : ons_decFirstReturnAtomExponent (atoms i) ≤ m := by
        rw [← hexponent]
        exact Finset.single_le_sum (fun j _ ↦
          (zero_le : (0 : ons_DecEdge L →₀ ℕ) ≤
            ons_decFirstReturnAtomExponent (atoms j)))
          (Finset.mem_univ i)
      have hdegree := ons_finsuppTotalDegree_mono hcomponent
      have hlength := ons_decLoopExponent_length_le L (atoms i).2.1
      change (atoms i).1 + 1 ≤
        ons_finsuppTotalDegree
          (ons_decFirstReturnAtomExponent (atoms i)) at hlength
      exact hlength.trans hdegree
    let bounded : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) :=
      fun i ↦ ⟨⟨(atoms i).1, by have := hbound i; omega⟩, (atoms i).2⟩
    have hbounded :
        (∑ i, ons_decBoundedAtomExponent (bounded i)) = m := by
      simpa only [bounded, ons_decBoundedAtomExponent,
        ons_decFirstReturnAtomExponent] using hexponent
    refine ⟨⟨bounded, hbounded⟩, ?_⟩
    apply Subtype.ext
    funext i
    rfl

end StatMech.Onsager
