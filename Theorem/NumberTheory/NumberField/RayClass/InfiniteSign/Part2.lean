/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InfiniteSign.lean -/

import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
import Lemma.Nat.NumberField.RayClass.RayGroup
import Mathlib.Data.ZMod.Basic
import Def.NumberTheory.NumberField.RayClass.InfiniteSign.Part2
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

/-- The sign at a real place is trivial iff the real embedding is positive. -/
@[simp] theorem signAtRealPlace_apply_eq_one_iff (w : RealPlace K) (x : Kˣ) :
    signAtRealPlace w x = 1 ↔
      0 < InfinitePlace.embedding_of_isReal w.property (x : K) := by
  unfold signAtRealPlace
  constructor
  · intro hcon
    change Multiplicative.ofAdd
        (signBit (InfinitePlace.embedding_of_isReal w.property (x : K))) = 1 at hcon
    by_cases hpos : 0 < InfinitePlace.embedding_of_isReal w.property (x : K)
    · exact hpos
    · rw [signBit_of_not_pos hpos] at hcon
      have h2 : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd hcon
      exact False.elim (one_ne_zero h2)
  · intro hpos
    change Multiplicative.ofAdd
        (signBit (InfinitePlace.embedding_of_isReal w.property (x : K))) = 1
    rw [signBit_of_pos hpos, ofAdd_zero_eq_one]

end Modulus
end NumberField
