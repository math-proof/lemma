import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec20NormalCodim2
open PrimeSpectrum


/--
[normal_codim2_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20NormalCodim2.lean)
-/
@[path]
lemma normal_codim2_extension
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsNoetherianRing R]
  [IsIntegrallyClosed R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I : Ideal R}
-- given
  (hI : 2 ≤ I.height) :
-- imply
  (⨅ (p : PrimeSpectrum R) (_ : ¬ (I ≤ p.asIdeal)), Localization.subalgebra.ofField K p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
-- proof
  apply le_antisymm
  ·
    rw [← Proposition39.iInf_heightOnePrime_localization_eq_bot (A := R) (K := K)]
    apply le_iInf
    intro q
    apply iInf_le_of_le ⟨q.asIdeal, q.isPrime⟩
    apply iInf_le_of_le (not_le_heightOnePrime_of_height_ge_two I hI q)
    exact le_refl _
  · exact bot_le

/--
[normal_codim2_extension_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20NormalCodim2.lean)
-/
@[path]
lemma normal_codim2_extension_mem
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsNoetherianRing R]
  [IsIntegrallyClosed R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I : Ideal R}
  {x : K}
-- given
  (hI : 2 ≤ I.height)
  (hx : ∀ (p : PrimeSpectrum R), ¬ (I ≤ p.asIdeal) → x ∈ Localization.subalgebra.ofField K p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors) :
-- imply
  x ∈ Set.range (algebraMap R K) := by
-- proof
  rw [← Algebra.mem_bot]
  rw [← normal_codim2_extension R K I hI]
  simp only [Algebra.mem_iInf]
  exact hx


-- created on 2026-10-23
