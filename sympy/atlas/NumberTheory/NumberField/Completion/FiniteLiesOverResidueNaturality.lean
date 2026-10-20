/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverResidueNaturality.lean -/

import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverResidueField
import sympy.atlas.RingTheory.DedekindDomain.AdicCompletionResidueField
/-!
# Explicit residue-field naturality square

## ATLAS source correspondence

This is the number-field/canonical-map version of
`completion_residueFieldEquiv_compat` at atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`,
[`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean`, lines 2248--2318](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2248-L2318).
That source
commutative square compares residue fields before and after completion:

```
(𝔭-completion integers)/𝔪𝔭  ─→  (𝔮-completion integers)/𝔪𝔮
              │                              │
              ▼                              ▼
                    A/𝔭  ───────────────→  B/𝔮.
```

Here `A = 𝓞 K`, `B = 𝓞 L`, `𝔭 = v.asIdeal`, and `𝔮 = w.asIdeal`.
The declarations map to the source clauses as follows:

* `ringOfIntegersResidueQuotientMap` is the lower source arrow, the quotient
  map induced by `algebraMap (𝓞 K) (𝓞 L)` and `w ∣ v`.
* `adicCompletionResidueQuotientMap` is the upper source arrow, induced by
  the canonical `adicCompletionIntegersMap v w`. Repaired #977 supplies the
  exact maximal-ideal contraction needed for this quotient map.
* `completionResidueFieldEquiv v` and `completionResidueFieldEquiv w` are the
  two vertical source equivalences `completion_residueFieldEquiv` from lines
  [2234--2243](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2234-L2243).
* `completionResidueFieldEquiv_naturality` is exactly the equality of the two
  composites in source
  [lines 2267--2278](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2267-L2278).
  Its representative calculation is the source calculation at
  [lines 2291--2318](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2291-L2318);
  repaired #981 supplies the
  pre-quotient algebra-map equality used in the middle of that calculation.

The explicit quotient homomorphisms avoid exposing arbitrary quotient
`Algebra` instances while preserving the same four objects and canonical maps.
This naturality square feeds `completion_residueField_finrank_eq` beginning at
source
[line 2324](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2324),
the residue-degree ingredient for the finite-place part of
N265, Theorem 13.5. The finrank equality and tensor-product decomposition are
outside this module's scope.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Global residue-field quotient map along `𝓞 K → 𝓞 L`. -/
noncomputable def ringOfIntegersResidueQuotientMap :
    𝓞 K ⧸ v.asIdeal →+* 𝓞 L ⧸ w.asIdeal :=
  Ideal.quotientMap w.asIdeal (algebraMap (𝓞 K) (𝓞 L)) (Ideal.over_def w.asIdeal v.asIdeal).le

/-- Completion residue-field quotient map along the adic integer map. -/
noncomputable def adicCompletionResidueQuotientMap :
    (↥(v.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers K)) →+*
      (↥(w.adicCompletionIntegers L) ⧸
        IsLocalRing.maximalIdeal ↥(w.adicCompletionIntegers L)) :=
  Ideal.quotientMap (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
    (adicCompletionIntegersMap v w)
    (comap_maximalIdeal_adicCompletionIntegersMap v w).ge

/-- Naturality of the residue-field equivalences with explicit quotient maps. -/
theorem completionResidueFieldEquiv_naturality :
    (ringOfIntegersResidueQuotientMap v w).comp
      (completionResidueFieldEquiv v).toRingHom =
    (completionResidueFieldEquiv w).toRingHom.comp
      (adicCompletionResidueQuotientMap v w) := by
  ext q
  obtain ⟨a, ha⟩ := surjective_completionResidueMap (K := K) v
    (Ideal.Quotient.mk _ q)
  simp only [RingHom.comp_apply]
  rw [← ha]
  have hdown : completionResidueFieldEquiv (K := K) v (completionResidueMap (K := K) v a) =
      Ideal.Quotient.mk v.asIdeal a := by
    simp only [completionResidueFieldEquiv, RingEquiv.trans_apply,
      RingHom.quotientKerEquivOfSurjective_symm_apply,
      Ideal.quotEquivOfEq_mk]
  have hup : completionResidueFieldEquiv (K := L) w
      (completionResidueMap (K := L) w (algebraMap (𝓞 K) (𝓞 L) a)) =
      Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 K) (𝓞 L) a) := by
    simp only [completionResidueFieldEquiv, RingEquiv.trans_apply,
      RingHom.quotientKerEquivOfSurjective_symm_apply,
      Ideal.quotEquivOfEq_mk]
  have hmid : adicCompletionResidueQuotientMap v w
      (completionResidueMap (K := K) v a) =
      completionResidueMap (K := L) w (algebraMap (𝓞 K) (𝓞 L) a) := by
    unfold adicCompletionResidueQuotientMap completionResidueMap
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk,
      adicCompletionIntegersMap_algebraMap v w a]
  have hdown' : (completionResidueFieldEquiv (K := K) v).toRingHom
      (completionResidueMap (K := K) v a) =
      Ideal.Quotient.mk v.asIdeal a := hdown
  have hup' : (completionResidueFieldEquiv (K := L) w).toRingHom
      (completionResidueMap (K := L) w (algebraMap (𝓞 K) (𝓞 L) a)) =
      Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 K) (𝓞 L) a) := hup
  simp only [hdown', hmid, hup']
  unfold ringOfIntegersResidueQuotientMap
  rw [Ideal.quotientMap_mk]

end IsDedekindDomain.HeightOneSpectrum

-- End of file.
