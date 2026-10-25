/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InfiniteSign.lean -/

import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
import Lemma.Nat.NumberField.RayClass.RayGroup
import Mathlib.Data.ZMod.Basic
import Theorem.NumberTheory.NumberField.RayClass.InfiniteSign
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

/-- Sign of a unit at a real place, valued in `Multiplicative (ZMod 2)`. -/
noncomputable def signAtRealPlace (w : RealPlace K) :
    Kˣ →* Multiplicative (ZMod 2) where
  toFun x :=
    Multiplicative.ofAdd
      (signBit (InfinitePlace.embedding_of_isReal w.property (x : K)))
  map_one' := by
    change Multiplicative.ofAdd
        (signBit (InfinitePlace.embedding_of_isReal w.property ((1 : Kˣ) : K))) =
        1
    rw [Units.val_one, map_one, signBit_of_pos one_pos, ofAdd_zero_eq_one]
  map_mul' := fun x y => by
    have hx : InfinitePlace.embedding_of_isReal w.property (x : K) ≠ 0 :=
      (map_ne_zero_iff _
        (RingHom.injective (InfinitePlace.embedding_of_isReal w.property))).mpr
        (Units.ne_zero x)
    have hy : InfinitePlace.embedding_of_isReal w.property (y : K) ≠ 0 :=
      (map_ne_zero_iff _
        (RingHom.injective (InfinitePlace.embedding_of_isReal w.property))).mpr
        (Units.ne_zero y)
    change Multiplicative.ofAdd
        (signBit
          (InfinitePlace.embedding_of_isReal w.property ((x * y : Kˣ) : K))) =
        Multiplicative.ofAdd
          (signBit (InfinitePlace.embedding_of_isReal w.property (x : K))) *
          Multiplicative.ofAdd
            (signBit (InfinitePlace.embedding_of_isReal w.property (y : K)))
    rw [Units.val_mul, map_mul, signBit_mul hx hy, ofAdd_add]

end Modulus
end NumberField
