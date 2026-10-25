/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean -/

/-
Author: @toskua, Avocado
-/

import Theorem.RingTheory.LocalRing.ResidueField.DVR.Part2
import Lemma.AlgHom.LocalRing.ResidueField.DVR
import Lemma.Polynomial.AdjoinRoot.LocalMaximal
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Separable
import Theorem.RingTheory.AdjoinRoot.LocalMaximal
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Def.RingTheory.LocalRing.ResidueField.AdjoinRootLift
open Polynomial

/-!
# Lifting irreducible residue polynomials over a DVR

This file develops the accumulated N211 AdjoinRoot construction: a monic
irreducible residue polynomial is lifted to a finite domain, its coefficient
quotient and residue field are identified, the lifted ring is made local and
then a discrete valuation ring, and finite separable residue extensions are
realized by finite local DVR extensions. These are the D1--D4 and object-
realization prerequisites, not the full categorical N211 equivalence.

Source map: this is ATLAS NumberTheoryI item N211, Theorem 10.13
(Section 10.2), Stage D1, at atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`; it is a prerequisite stage and
not the full N211 target. The
[English target is `v1/Atlas/NumberTheoryI/targets.yaml`, lines 1466-1483](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1466-L1483);
its essential-surjectivity clause says every finite separable residue-field
extension is realized by an unramified extension. The implementation target is
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean):
the source construction helper
[`adjoinRoot_dvr_of_irreducible_lift` (lines 349-453)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L349-L453)
and the caller
[`residueFieldFunctor_essential_surjectivity` (lines 1174-1203)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1174-L1203),
which chooses
a primitive element and its monic irreducible separable minimal polynomial
([lines 1187-1193](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1187-L1193))
and then invokes the construction helper
([lines 1196-1198](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1196-L1198)).

The D1 theorem below extracts exactly
[lines 364-377 of the source helper](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L364-L377).
`DVRResidue.exists_monic_lift_adjoinRoot_domain` takes a monic irreducible
polynomial `gbar` over `IsLocalRing.ResidueField A` and returns a monic
`g : A[X]` with exact reduction `g.map (IsLocalRing.residue A) = gbar`, plus
`IsDomain (AdjoinRoot g)` and `Module.Finite A (AdjoinRoot g)`. The proof
chain is: coefficientwise residue surjectivity yields
`gbar ∈ Polynomial.lifts`; `lifts_and_natDegree_eq_and_monic` produces `g`;
the exact reduction transports irreducibility;
`Polynomial.Monic.irreducible_of_irreducible_map`, DVR/UFD
irreducible-to-prime, and `AdjoinRoot.isDomain_of_prime` produce the domain;
`g.Monic.finite_adjoinRoot` gives finiteness.

The source helper's `HenselianLocalRing A` and `gbar.Separable` hypotheses
are unused in this extracted portion and are therefore omitted. The unused
returned natDegree equality is also not exposed. Those omitted hypotheses are not needed for D1
itself. The subsequent sections
provide locality, quotient/residue-field equivalences, the DVR structure, and
the finite-separable object-realization package. They still do not prove the
unramified/étale structure or the full categorical equivalence. Monic plus
irreducible reduction alone need not imply separability, and domain plus
finiteness alone does not imply `Algebra.Etale`.

Stage D2 corresponds exactly to the quotient construction in
[`ResidueFieldFunctor.adjoinRoot_dvr_of_irreducible_lift`, lines
386--407](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L386-L407).
There the source first identifies the maximal ideal of `AdjoinRoot g` with
the image of the coefficient-ring maximal ideal (`e1`), then factors the
residue-field equivalence into

1. `e2`, lines 396--399: quotienting `AdjoinRoot g` coefficientwise gives
   the quotient polynomial ring over `ResidueField A`; and
2. `e3`, lines 401--404: the exact reduction equation
   `g.map (residue A) = gbar` identifies that reduced polynomial with `gbar`.

`adjoinRootQuotientEquivOfMapEq` is precisely the canonical composite
`e2.trans e3`, exposed before the local/DVR step. Its domain is
`AdjoinRoot g` modulo the image of `maximalIdeal A`, its codomain is
`AdjoinRoot gbar`, and `adjoinRootQuotientEquivOfMapEq_mk` records its action
on a polynomial representative: reduce every coefficient and then apply
`AdjoinRoot.mk`. The required reduction equality is the final fact returned
by Stage D1. The source's `e1` (identifying this coefficient quotient with the
actual residue field of `AdjoinRoot g`) is deliberately not claimed here; it
requires the locality/maximal-ideal stage that follows.

Stage D3 supplies exactly that missing local layer. Its primary source is
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
at the same commit:

* [`adjoinRoot_isLocalRing_of_irred_map`, lines 211--244](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L211-L244), constructs the unique
  maximal ideal of `AdjoinRoot g` from monicity, finiteness, and irreducibility
  of the reduced polynomial;
* [`adjoinRoot_map_maximalIdeal_isMaximal`, lines 279--293](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L279-L293), proves that the image
  of the coefficient-ring maximal ideal is maximal;
* [`adjoinRoot_maxIdeal_eq_map_of_irred`, lines 339--347](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L339-L347), identifies it with the
  actual maximal ideal upstairs; and
* [`e1` followed by `e2.trans e3`, lines 386--407](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L386-L407), identifies the residue field
  of `AdjoinRoot g` with `AdjoinRoot gbar`.

The `adjoinRoot_*` declarations below specialize those three source helpers to
an arbitrary local coefficient ring using the stronger N209 classification
provided by `MathlibExt.RingTheory.AdjoinRoot.LocalMaximal`.
`residueFieldEquivAdjoinRootOfMapEq` is source `e1.trans (e2.trans e3)`:
the D3 maximal-ideal equality supplies `e1`, while D2 supplies `e2.trans e3`.
Its `_residue_mk` theorem records the canonical action on polynomial
representatives. D1 supplies monicity, finiteness, domainhood, and the exact
reduction equation; D2 supplies the coefficient quotient equivalence; N209
supplies maximal-ideal classification. This stage still does not construct
the DVR, local-hom, finite-dimensional, separable, or full
essential-surjectivity packages returned later in
[source lines 349--453](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L349-L453).

Stage D4 is the DVR conclusion for a monic `AdjoinRoot` whose residue
reduction is irreducible, after the domain and local-ring structures are
installed. Its exact source is
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`, helper
`adjoinRoot_isDVR_of_irred_map`, lines 295--321](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L295-L321).
The source hypothesis that
`A` is a DVR maps to `[CommRing A] [IsDomain A]
[IsDiscreteValuationRing A]`; source monicity maps to `hg : g.Monic`; and
irreducibility of the residue reduction maps to
`hirr : Irreducible (g.map (IsLocalRing.residue A))`. The instance
`[IsDomain (AdjoinRoot g)]` is supplied by D1 and
`[IsLocalRing (AdjoinRoot g)]` by D3. The source's explicit finite-module
hypothesis is derived here from `hg.finite_adjoinRoot`, after which the proof
derives Noetherianity, excludes the field case, identifies the maximal ideal
using D3, proves it principal, and applies `IsDiscreteValuationRing.TFAE`.
The exact conclusion is
`DVRResidue.adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map`.
D4 is only a prerequisite stage and does not prove the later local-hom,
finite-dimensional, separable, essential-surjectivity, full-faithfulness, or
categorical equivalence clauses.

The essential-surjectivity object stage is the finite-separable
residue-extension object-realization step only. Its source module is
`Atlas.NumberTheoryI.ResidueFieldFunctor`, source file
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`, matched declaration
`residueFieldFunctor_essential_surjectivity`, lines 1174--1203](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1174-L1203).
The source
chooses a primitive element and its monic irreducible separable minimal
polynomial at lines 1187--1193, invokes `adjoinRoot_dvr_of_irreducible_lift`
at lines 1196--1198, and composes the resulting residue-field equivalence at
lines 1200--1203.

The source data maps to
`DVRResidue.exists_finite_dvr_extension_residueField_algEquiv` as follows:
the finite-dimensional separable residue-field extension is `L` with
`[Field L]`, `[Algebra (IsLocalRing.ResidueField A) L]`,
`[FiniteDimensional (IsLocalRing.ResidueField A) L]`, and
`[Algebra.IsSeparable (IsLocalRing.ResidueField A) L]`; the constructed ring
is `B` with `[CommRing B]`, `[IsDomain B]`, `[Algebra A B]`,
`[Module.Finite A B]`, `[IsDiscreteValuationRing B]`, and
`[IsLocalHom (algebraMap A B)]`; the residue comparison is
`Nonempty (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L)`.

The source assumes `[HenselianLocalRing A]`, with completeness supplying that
upstream. This stage omits Henselianity/completeness only because it proves
the weaker ring-level object realization and does not package or prove an
unramified extension object. It therefore does not yet establish the full
categorical essential-surjectivity clause, full faithfulness, or the N211
equivalence.

Public theorems:
* `DVRResidue.exists_monic_lift_adjoinRoot_domain`
* `DVRResidue.adjoinRootQuotientEquivOfMapEq`
* `DVRResidue.adjoinRootQuotientEquivOfMapEq_mk`
* `DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map`
* `DVRResidue.adjoinRoot_map_maximalIdeal_isMaximal`
* `DVRResidue.maximalIdeal_adjoinRoot_eq_map`
* `DVRResidue.residueFieldEquivAdjoinRootOfMapEq`
* `DVRResidue.adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map`
* `DVRResidue.adjoinRoot_isLocalHom_of_irreducible_map`
* `DVRResidue.residueFieldAlgEquivAdjoinRootOfMapEq`
* `DVRResidue.residueFieldAlgEquivAdjoinRootOfMapEq_residue_mk`
* `DVRResidue.exists_finite_dvr_extension_residueField_algEquiv`
-/


namespace DVRResidue

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

section QuotientEquiv

@[simp]
theorem adjoinRootQuotientEquivOfMapEq_mk
    (g : R[X]) (gbar : (IsLocalRing.ResidueField R)[X])
    (hmap : g.map (IsLocalRing.residue R) = gbar) (p : R[X]) :
    adjoinRootQuotientEquivOfMapEq g gbar hmap
        (Ideal.Quotient.mk _ (AdjoinRoot.mk g p)) =
      AdjoinRoot.mk gbar (p.map (IsLocalRing.residue R)) := by
  subst gbar
  exact AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of
    (I := IsLocalRing.maximalIdeal R) (f := g) p

end QuotientEquiv

section Local

variable {A : Type*} [CommRing A] [IsLocalRing A] {g : A[X]}

/-- The image of the base maximal ideal in `AdjoinRoot g` is maximal. -/
theorem adjoinRoot_map_maximalIdeal_isMaximal
    (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
    (Ideal.map (algebraMap A (AdjoinRoot g))
      (IsLocalRing.maximalIdeal A)).IsMaximal := by
  have h := AdjoinRoot.is_maximal_of_irreducible_factor g g hirr dvd_rfl
  simpa [AdjoinRoot.mk_self] using h

/-- The maximal ideal upstairs is the image of the base maximal ideal. -/
theorem maximalIdeal_adjoinRoot_eq_map [IsLocalRing (AdjoinRoot g)]
    (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
    IsLocalRing.maximalIdeal (AdjoinRoot g) =
      Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal A) := by
  have h : (Ideal.map (algebraMap A (AdjoinRoot g))
      (IsLocalRing.maximalIdeal A)).IsMaximal :=
    adjoinRoot_map_maximalIdeal_isMaximal (g := g) hirr
  have heq : IsLocalRing.maximalIdeal (AdjoinRoot g) =
      Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) :=
    (IsLocalRing.eq_maximalIdeal h).symm
  simpa only [AdjoinRoot.algebraMap_eq] using heq

end Local
end DVRResidue
