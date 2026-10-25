/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part23


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRAugmentedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N : ℕ}


@[simp] theorem lower_tail (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    (H.lower d).tail = H.lowerCore d := rfl

@[simp] theorem upper_tail (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    (H.upper d).tail = H.upperCore d := rfl


@[simp] theorem decode_augmented
    (H : HLHRAugmentedTwoHalfData a h0 N) (d : hhc_Dn a h0 N) :
    H.decode (H.lower d).head! (H.lower d).tail
      (H.upper d).head! (H.upper d).tail = d.1 := by
  exact H.decode_source d


theorem length_add_two (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    (H.lower d).length + (H.upper d).length = d.1.length + 2 := by
  simp only [lower, upper, List.length_cons]
  have hlen := H.core_length d
  omega


theorem lowerBoundary_legal (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    H.lowerBoundary d = 1 ∨ H.lowerBoundary d = -1 := by
  exact (H.lower_legal d).1 _ (by simp [lower])


theorem upperBoundary_legal (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    H.upperBoundary d = 1 ∨ H.upperBoundary d = -1 := by
  exact (H.upper_legal d).1 _ (by simp [upper])


theorem lowerBoundary_outward (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    hlhr_height 0 (H.lower d) 0 < hlhr_height 0 (H.lower d) 1 := by
  apply H.lower_halfSpace d 1 (by omega)
  simp [lower]


theorem upperBoundary_outward (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    hlhr_height 0 (H.upper d) 0 < hlhr_height 0 (H.upper d) 1 := by
  apply H.upper_halfSpace d 1 (by omega)
  simp [upper]


theorem listPair_injective (H : HLHRAugmentedTwoHalfData a h0 N) :
    Function.Injective (fun d => (H.lower d, H.upper d)) := by
  intro d e hpair
  apply Subtype.ext
  rw [← H.decode_source d, ← H.decode_source e]
  have hlo := congrArg Prod.fst hpair
  have hup := congrArg Prod.snd hpair
  have hlo' := List.cons.inj (by simpa [lower] using hlo)
  have hup' := List.cons.inj (by simpa [upper] using hup)
  rw [hlo'.1, hlo'.2, hup'.1, hup'.2]


end HLHRAugmentedTwoHalfData
end StatMech.Universality
