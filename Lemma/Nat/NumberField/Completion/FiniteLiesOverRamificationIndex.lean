import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.NumberTheory.NumberField.Completion.FiniteLiesOverInertiaDegree
import Lemma.Nat.NumberField.Completion.FiniteLiesOverInertiaDegree
open scoped WithZero NumberField NumberField.LiesOver


namespace IsDedekindDomain.HeightOneSpectrum

variable [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))
/--
[valued_irreducible_eq_exp_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverRamificationIndex.lean)
-/
@[path]
private lemma valued_irreducible_eq_exp_neg_one
  {pi : v.adicCompletionIntegers F} (hpi : Irreducible pi) :
  Valued.v (pi : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  have hU : Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
    (pi : v.adicCompletion F) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span _ hpi.maximalIdeal_eq
  rw [Valuation.IsUniformizer.val hU]
  exact congrArg Units.val
    (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (valuedAdicCompletion_surjective F v))

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[adicCompletionIntegersMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverRamificationIndex.lean)
-/
@[path]
lemma adicCompletionIntegersMap_injective
  [Field F] [NumberField F] [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  Function.Injective (adicCompletionIntegersMap v w) := by
-- proof
  intro x y h
  apply Subtype.ext
  apply adicCompletionMap_injective v w
  simpa only [adicCompletionIntegersMap_apply] using congrArg Subtype.val h

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[ramificationIdx_adicCompletionIntegersMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverRamificationIndex.lean)
-/
@[path]
lemma ramificationIdx_adicCompletionIntegersMap
  [Field F] [NumberField F] [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
    (v.adicCompletionIntegers K) =
    w.asIdeal.ramificationIdx (𝓞 K) := by
-- proof
  let _ : Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
    (adicCompletionIntegersMap v w).toAlgebra
  have halg : algebraMap (v.adicCompletionIntegers K)
    (w.adicCompletionIntegers L) = adicCompletionIntegersMap v w := rfl
  let _ : FaithfulSMul (v.adicCompletionIntegers K)
    (w.adicCompletionIntegers L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (halg ▸ adicCompletionIntegersMap_injective v w)
  let _ : Module.IsTorsionFree (v.adicCompletionIntegers K)
    (w.adicCompletionIntegers L) := inferInstance
  let _ : IsLocalHom (algebraMap (v.adicCompletionIntegers K)
    (w.adicCompletionIntegers L)) :=
    IsLocalHom.mk (fun x hx => by
      by_contra hxnu
      have hxmem : x ∈ IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers K) :=
        (IsLocalRing.mem_maximalIdeal x).mpr ((mem_nonunits_iff).mpr hxnu)
      have hcomap := comap_maximalIdeal_adicCompletionIntegersMap v w
      have himg : algebraMap (v.adicCompletionIntegers K)
        (w.adicCompletionIntegers L) x ∈ IsLocalRing.maximalIdeal
        (w.adicCompletionIntegers L) := by
        rw [halg]
        have hmem : x ∈ Ideal.comap (adicCompletionIntegersMap v w)
          (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) := by
          rwa [hcomap]
        exact hmem
      exact (((mem_nonunits_iff).mp ((IsLocalRing.mem_maximalIdeal _).mp himg)) hx))
  obtain ⟨pi_v, hpi_v⟩ :=
    IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨pi_w, hpi_w⟩ :=
    IsDiscreteValuationRing.exists_irreducible (w.adicCompletionIntegers L)
  have hval : Valued.v
    ((adicCompletionIntegersMap v w pi_v : w.adicCompletionIntegers L) :
      w.adicCompletion L) =
    Valued.v (((pi_w ^ w.asIdeal.ramificationIdx (𝓞 K) :
      w.adicCompletionIntegers L)) : w.adicCompletion L) := by
    rw [adicCompletionIntegersMap_apply, valuation_adicCompletionMap,
      valued_irreducible_eq_exp_neg_one v hpi_v]
    change _ = Valued.v ((pi_w : w.adicCompletion L) ^ w.asIdeal.ramificationIdx (𝓞 K))
    rw [map_pow,
      valued_irreducible_eq_exp_neg_one w hpi_w,
      Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  have hassoc : Associated (adicCompletionIntegersMap v w pi_v)
    (pi_w ^ w.asIdeal.ramificationIdx (𝓞 K)) := by
    have hv : Valuation.Integers (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)
      (w.adicCompletionIntegers L) :=
      Valuation.valuationSubring.integers _
    apply associated_of_dvd_dvd
    · exact hv.dvd_of_le (by
      change Valued.v (((pi_w ^ w.asIdeal.ramificationIdx (𝓞 K) :
        w.adicCompletionIntegers L)) : w.adicCompletion L) ≤
        Valued.v (((adicCompletionIntegersMap v w pi_v :
          w.adicCompletionIntegers L)) : w.adicCompletion L)
      exact hval.ge)
    · exact hv.dvd_of_le (by
      change Valued.v (((adicCompletionIntegersMap v w pi_v :
        w.adicCompletionIntegers L)) : w.adicCompletion L) ≤
        Valued.v (((pi_w ^ w.asIdeal.ramificationIdx (𝓞 K) :
          w.adicCompletionIntegers L)) : w.adicCompletion L)
      exact hval.le)
  have hadd : IsDiscreteValuationRing.addVal (w.adicCompletionIntegers L)
    (algebraMap (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) pi_v) =
    IsDiscreteValuationRing.addVal (w.adicCompletionIntegers L)
      (pi_w ^ w.asIdeal.ramificationIdx (𝓞 K)) := by
    have hassoc' : Associated (algebraMap (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) pi_v)
      (pi_w ^ w.asIdeal.ramificationIdx (𝓞 K)) := halg ▸ hassoc
    have h := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr hassoc'
    exact h
  rw [hpi_w.addVal_pow] at hadd
  have hscale := IsDiscreteValuationRing.addVal_algebraMap_eq_ramificationIdx_mul
    (A := v.adicCompletionIntegers K) (B := w.adicCompletionIntegers L) pi_v
  rw [halg] at hscale hadd
  simp only [IsDiscreteValuationRing.addVal_uniformizer hpi_v, mul_one] at hscale
  have hchain : ((IsLocalRing.maximalIdeal
    (w.adicCompletionIntegers L)).ramificationIdx
    (v.adicCompletionIntegers K) : ℕ∞) =
    ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : ℕ∞) := by
    rw [← hadd, hscale]
  exact ENat.natCast_inj.mp hchain

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-26
