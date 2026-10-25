/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean -/

/-
Author: Muse Code
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Def.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece
import Lemma.Int.DiscreteValuationRing.MaximalIdealGradedPiece
import Abbrev.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor
open IsLocalRing

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]

/-!
# Residue-field quotients of a DVR extension by maximal-ideal powers

Let `A` and `B` be commutative-domain discrete valuation rings with an
`A`-algebra structure on `B`. For each `n`, this file defines the canonical
quotient of `B` by `map 𝔪A ⊔ 𝔪B ^ n` and equips it with its canonical
`ResidueField A`-algebra structure, together with the canonical factor map
from index `n + 1` to index `n` and its surjectivity.

ATLAS source (item NumberTheoryI N261):
[`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines set up the ramification/different valuations for the corrected
quotient-filtration proof; they state no quotient-tower API.

Source-to-API map: for NumberTheoryI N261, the public declarations
`ResidueFieldMaximalIdealPowQuotient`, `instAlgebraQuot`,
`instAlgebraResidue`, `maximalIdealPowQuotientIdeal_le`,
`factorResidueFieldMaximalIdealPowQuotient`,
`factorResidueFieldMaximalIdealPowQuotient_surjective`,
`factorResidueFieldMaximalIdealPowQuotient_mk`,
`maximalIdealPowQuotientIdeal_eq`,
`residueFieldMaximalIdealPowQuotientEquivPow`,
`residueFieldMaximalIdealPowQuotientEquivPow_mk`,
`residueFieldLinearEquivMaximalIdealGradedPieceKerFactor`, and
`residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk` are new
supporting API for the quotient-filtration route, not declarations present
in the pinned ATLAS lines 1237--1324.

This file is new supporting API (prerequisite infrastructure for the corrected
quotient-filtration proof), not a theorem stated in ATLAS and not the final
different-exponent bound.

## Public declarations

* `ResidueFieldMaximalIdealPowQuotient`: the quotient
  `B ⧸ (map 𝔪A ⊔ 𝔪B ^ n)`.
* `instAlgebraQuot`: the canonical `A ⧸ 𝔪A`-algebra structure, via
  `Ideal.Quotient.algebraQuotientOfLEComap`.
* `instAlgebraResidue`: the `ResidueField A`-algebra structure, transported
  along the definitional unfolding `ResidueField A = A ⧸ 𝔪A`.
* `maximalIdealPowQuotientIdeal_le`: the containment
  `map 𝔪A ⊔ 𝔪B ^ (n + 1) ≤ map 𝔪A ⊔ 𝔪B ^ n`.
* `maximalIdealPowQuotientIdeal_eq`: under `map 𝔪A ≤ 𝔪B ^ n`, the defining
  ideal `map 𝔪A ⊔ 𝔪B ^ n` equals `𝔪B ^ n`.
* `factorResidueFieldMaximalIdealPowQuotient`: the canonical
  `ResidueField A`-algebra factor map from index `n + 1` to index `n`.
* `factorResidueFieldMaximalIdealPowQuotient_surjective`: surjectivity of the
  factor map.
* `factorResidueFieldMaximalIdealPowQuotient_mk`: the factor map fixes
  quotient representatives.
* `residueFieldMaximalIdealPowQuotientEquivPow`: under
  `map 𝔪A ≤ 𝔪B ^ n`, the ring equivalence with `B ⧸ 𝔪B ^ n`.
* `residueFieldMaximalIdealPowQuotientEquivPow_mk`: the equivalence fixes
  quotient representatives.
* `residueFieldLinearEquivMaximalIdealGradedPieceKerFactor`: under
  `map 𝔪A ≤ 𝔪B ^ (n + 1)`, the `ResidueField A`-linear equivalence between
  the `n`-th maximal-ideal graded piece of `B` and the kernel of the factor
  map from index `n + 1` to index `n`.
* `residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk`: the kernel
  equivalence sends a graded representative to the corresponding quotient
  representative.

Deferred to later stages: the trace recurrence, the full quotient trace
formula, the different containment, and the valuation bounds.
-/


/-- Canonical `(A ⧸ 𝔪A)`-algebra structure on the quotient, from
`Ideal.Quotient.algebraQuotientOfLEComap` applied to
`Ideal.map_le_iff_le_comap.mp le_sup_left`. -/
instance instAlgebraQuot (n : ℕ) :
    Algebra (A ⧸ maximalIdeal A) (ResidueFieldMaximalIdealPowQuotient A B n) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp le_sup_left)

/-- Residue-field scalar action on the quotient, transported along the
definitional unfolding `ResidueField A = A ⧸ 𝔪A` from the generic
`Algebra (A ⧸ 𝔪A)` instance (typeclass resolution does not unfold the plain
`ResidueField` def on its own). -/
instance instAlgebraResidue (n : ℕ) :
    Algebra (ResidueField A) (ResidueFieldMaximalIdealPowQuotient A B n) :=
  inferInstanceAs (Algebra (A ⧸ maximalIdeal A) _)

