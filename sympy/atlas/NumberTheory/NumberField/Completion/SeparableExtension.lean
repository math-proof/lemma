/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/SeparableExtension.lean -/

/-
Author: Muse Code
-/

import sympy.atlas.Analysis.Normed.Field.AdjoinRootStability
import sympy.atlas.NumberTheory.NumberField.Completion.GlobalAdjoinRootCompletionEquiv
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import sympy.atlas.FieldTheory.SeparableAdjoinRoot
import sympy.atlas.NumberTheory.NumberField.Completion.FinitePlacesOver
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# Finite-place number-field clause of ATLAS Theorem 11.20

Final finite-place assembly: every finite separable extension `M` of the
`v`-adic completion of a number field is `K_v`-algebra-equivalent to the
`w`-adic completion of a number-field extension, at a finite place `w`
lying over `v`, with matching degrees.

## ATLAS source-to-API map

* ATLAS source: `v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 600--689
  (atlas-lean commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`):
  <https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L600-L689>
* Campaign target: ATLAS node N234; internal campaign stage N234-B7:
  <https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1647-L1655>,
  the finite-place number-field clause of ATLAS Theorem 11.20.
* Mathematical source: MIT 18.785 *Number Theory I*, Lecture 11, Theorem 11.20:
  <https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/mit18_785f21_lec11.pdf>

Line-by-line correspondence:

* Lines 600--615 (statement): a finite separable `M / K_v` yields `L / K`
  with `w` over `v`, equal degrees, and `M ≃ L_w`. This is
  `separableExtension_isCompletion_finitePlace` below.
* Lines 621--628 (primitive element and minpoly data): these choose the
  primitive element and its minpoly data, formalized as
  `Algebra.isSeparable_iff_exists_monic_irreducible_separable`; degree
  identification occurs at lines 656--658 and is derived in this theorem
  from the returned equivalence, while construction of `M ≃ AdjoinRoot f`
  is specifically lines 677--679.
* Lines 633--635 (Krasner stability radius): `Theorem_11_19` applied to `f`.
  Formalized as
  `Polynomial.exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt` (PR #1415).
* Lines 637--638 (dense approximation): global monic `g` close to `f`.
  Formalized as
  `Polynomial.exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable`
  (PR #1412), applied to `v.denseRange_algebraMap K`.
* Lines 640--654 (mapped data and irreducibility descent): these establish mapped
  monicity/degree/irreducibility and descend irreducibility to global `g`
  via `Polynomial.Monic.irreducible_of_irreducible_map`.
* Lines 661--682 (equal adjoin and equivalence): the
  equal-adjoin/`AdjoinRoot` equivalence and its composition with
  `M ≃ AdjoinRoot f`.
* Global `L`, `w`, and the completion identification are implemented in
  lines 550--598 and invoked at lines 684--689; the degree equality
  `finrank K L = finrank K_v M` goes via
  `finrank_quotient_span_eq_natDegree`, and the completion identification
  via `completion_algEquiv_of_adjoinRoot_globalEquiv`
  (merged #1403--#1406).
* The admitted inputs at lines 418--466 are replaced by formal-math's
  completion APIs.

## Deliberate stronger packaging

ATLAS returns raw `w`, a contraction equality, and an existential arbitrary
completion `Algebra`; the theorem instead returns `w.asIdeal.LiesOver
v.asIdeal` (the same contraction equality in its stored orientation) and
uses the canonical scoped `NumberField.LiesOver` completion algebra.

## Scope

This completes the finite-place number-field clause of the formal ATLAS
declaration of Theorem 11.20. It does not cover the infinite-place clause,
function-field generality, topological/isometric equivalence, or the prose
compositum identity.
-/

universe u v

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

open scoped NumberField NumberField.LiesOver Valued

theorem separableExtension_isCompletion_finitePlace
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (M : Type v) [Field M] [Algebra (v.adicCompletion K) M]
    [FiniteDimensional (v.adicCompletion K) M]
    [Algebra.IsSeparable (v.adicCompletion K) M] :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L)
      (w : HeightOneSpectrum (𝓞 L))
      (hw : w.asIdeal.LiesOver v.asIdeal),
      let _ : w.asIdeal.LiesOver v.asIdeal := hw
      Module.finrank K L =
          Module.finrank (v.adicCompletion K) M ∧
        Nonempty (M ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
  obtain ⟨f, hf, hirr, hsep, ⟨eMf⟩⟩ :=
    (Algebra.isSeparable_iff_exists_monic_irreducible_separable
      (v.adicCompletion K) M).mp inferInstance
  obtain ⟨δ, hδ, hstable⟩ :=
    Polynomial.exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt
      (v.adicCompletion K) f hf hirr hsep
  obtain ⟨g, hg, hdeg, hclose, hmapirr, _⟩ :=
    Polynomial.exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable
      (v.denseRange_algebraMap K) f hf hirr hsep hδ
  obtain ⟨efg⟩ :=
    hstable (g.map (algebraMap K (v.adicCompletion K)))
      (hg.map _) hclose
  have hgirr : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (algebraMap K (v.adicCompletion K)) g hg hmapirr
  let _ : Fact (Irreducible g) := ⟨hgirr⟩
  let L := AdjoinRoot g
  let _ : Module.Finite K L :=
    (AdjoinRoot.powerBasis hgirr.ne_zero).finite
  let _ : NumberField L :=
    NumberField.of_module_finite K L
  let _ : Algebra.IsSeparable K L := inferInstance
  let _ : FiniteDimensional K L := inferInstance
  let vw : v.placesOver L := Classical.choice inferInstance
  let w := vw.val
  let _ : w.asIdeal.LiesOver v.asIdeal := vw.property
  have hfinrankL : Module.finrank K L = g.natDegree := by
    dsimp [L]
    exact finrank_quotient_span_eq_natDegree
  have hfinrankM :
      Module.finrank (v.adicCompletion K) M = f.natDegree := by
    calc
      Module.finrank (v.adicCompletion K) M =
          Module.finrank (v.adicCompletion K) (AdjoinRoot f) :=
        eMf.toLinearEquiv.finrank_eq
      _ = f.natDegree := finrank_quotient_span_eq_natDegree
  have hfinrank :
      Module.finrank K L =
        Module.finrank (v.adicCompletion K) M := by
    rw [hfinrankL, hfinrankM, hdeg]
  let eL : L ≃ₐ[K] AdjoinRoot g := by
    dsimp [L]
    exact AlgEquiv.refl
  have hM :
      Nonempty
        (M ≃ₐ[v.adicCompletion K]
          AdjoinRoot
            (g.map (algebraMap K (v.adicCompletion K)))) :=
    ⟨eMf.trans efg⟩
  have hcompletion :
      Nonempty (M ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
    completion_algEquiv_of_adjoinRoot_globalEquiv
      v w g hmapirr eL hM
  exact
    ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, w, inferInstance, hfinrank, hcompletion⟩

end IsDedekindDomain.HeightOneSpectrum
