/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InfiniteSign.lean -/

import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
import Lemma.Nat.NumberField.RayClass.RayGroup
import Mathlib.Data.ZMod.Basic
import Def.NumberTheory.NumberField.RayClass.InfiniteSign
@[expose] noncomputable section

/-!
# Infinite-place signs for ray class groups (N406 stage 1a)

The first coordinate of the later residue-sign map: the sign of a ray element
at each real place selected by a modulus, valued in `Multiplicative (ZMod 2)`.

ATLAS source map: NumberTheoryI item N406, Theorem 21.8, Section 21.3, source
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, declaration
`RayClassField.theorem_21_8_quotient_iso`:
https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647

* `signAtRealPlace` corresponds to ATLAS `signAtPlace` with
  `signAtPlace_eq_zero_iff` (lines 1497--1531): trivial sign is strict
  positivity at the selected real embedding.
* `infiniteSignMap` corresponds to ATLAS `signMapHom` (lines 1533--1551):
  it collects the sign coordinates over the modulus's infinite support.
* `positiveRayElements := (infiniteSignMap m).ker` packages the
  infinite-positivity conjunct of ATLAS `UnitsCongruent_subgroup'`
  (lines 827--839), and `mem_positiveRayElements_iff` is the native
  kernel/positivity bridge used by the final product-map kernel calculation
  (lines 2612--2643).

Scope: this module provides only the infinite-sign coordinate toward the
residue-sign product and quotient equivalence. It does not complete all of
N406, including the finite coordinate, surjectivity, quotient equivalence,
or exact sequence.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- The sign bit of a positive real number is `0`. -/
theorem signBit_of_pos {r : ℝ} (h : 0 < r) : signBit r = 0 := ite_eq_left h

/-- The sign bit of a non-positive real number is `1`. -/
theorem signBit_of_not_pos {r : ℝ} (h : ¬ 0 < r) : signBit r = 1 :=
  ite_eq_right h

/-- The sign bit is multiplicative on nonzero reals. -/
theorem signBit_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    signBit (a * b) = signBit a + signBit b := by
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
  · rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
    · have hpos : 0 < a * b := mul_pos_of_neg_of_neg ha_neg hb_neg
      rw [signBit_of_pos hpos, signBit_of_not_pos (not_lt_of_gt ha_neg),
        signBit_of_not_pos (not_lt_of_gt hb_neg)]
      decide
    · have hneg : a * b < 0 := mul_neg_of_neg_of_pos ha_neg hb_pos
      rw [signBit_of_not_pos (not_lt_of_gt hneg),
        signBit_of_not_pos (not_lt_of_gt ha_neg), signBit_of_pos hb_pos]
      decide
  · rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
    · have hneg : a * b < 0 := mul_neg_of_pos_of_neg ha_pos hb_neg
      rw [signBit_of_not_pos (not_lt_of_gt hneg), signBit_of_pos ha_pos,
        signBit_of_not_pos (not_lt_of_gt hb_neg)]
      decide
    · have hpos : 0 < a * b := mul_pos ha_pos hb_pos
      rw [signBit_of_pos hpos, signBit_of_pos ha_pos, signBit_of_pos hb_pos]
      decide

/-- `ofAdd 0` is the identity of `Multiplicative (ZMod 2)`. -/
theorem ofAdd_zero_eq_one : Multiplicative.ofAdd (0 : ZMod 2) = 1 := rfl

end Modulus
end NumberField
