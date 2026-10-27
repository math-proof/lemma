import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.PolarDensity
open Filter Topology NumberField IsDedekindDomain
open NumberField.Set


namespace NumberField.Set

variable [Field K] [NumberField K]
/--
[eventuallyEq_nhdsNE_of_eventuallyEq_re_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PolarDensity.lean)
-/
@[path]
private lemma eventuallyEq_nhdsNE_of_eventuallyEq_re_gt_one
  {f g : ℂ → ℂ} (hf : MeromorphicAt f (1 : ℂ))
  (hg : MeromorphicAt g (1 : ℂ))
  (hfg : f =ᶠ[nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}] g) :
  f =ᶠ[𝓝[≠] (1 : ℂ)] g := by
  apply (hf.frequently_eq_iff_eventuallyEq hg).mp
  have hcl : (1 : ℂ) ∈ closure {z : ℂ | (1 : ℝ) < z.re} := by
    rw [Complex.closure_setOfPred_lt_re]
    simp
  let : NeBot (nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}) :=
    mem_closure_iff_nhdsWithin_neBot.mp hcl
  exact hfg.frequently.filter_mono <| nhdsWithin_mono (1 : ℂ) <| by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    simp at hz

end NumberField.Set

namespace NumberField.Set

/--
[HasPolarDensity.unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PolarDensity.lean)
-/
@[path]
lemma HasPolarDensity.unique
  [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {ρ₁ ρ₂ : ℚ}
-- given
  (h₁ : S.HasPolarDensity ρ₁)
  (h₂ : S.HasPolarDensity ρ₂) :
-- imply
  ρ₁ = ρ₂ := by
-- proof
  obtain ⟨n₁, m₁, F₁, hmer₁, hcont₁, hord₁, rfl⟩ := h₁
  obtain ⟨n₂, m₂, F₂, hmer₂, hcont₂, hord₂, rfl⟩ := h₂
  have hpow : F₁ ^ (n₂ : ℕ) =ᶠ[nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}]
    F₂ ^ (n₁ : ℕ) := by
    filter_upwards [hcont₁, hcont₂] with z hz₁ hz₂
    simp only [Pi.pow_apply]
    rw [hz₁, hz₂, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hne := eventuallyEq_nhdsNE_of_eventuallyEq_re_gt_one
    (hmer₁.pow _) (hmer₂.pow _) hpow
  have hord := meromorphicOrderAt_congr hne
  rw [meromorphicOrderAt_pow hmer₁, meromorphicOrderAt_pow hmer₂,
    hord₁, hord₂] at hord
  have horderZ : ((n₂ : ℕ) : ℤ) * (-m₁) = ((n₁ : ℕ) : ℤ) * (-m₂) := by
    exact_mod_cast hord
  have hint : m₁ * ((n₂ : ℕ) : ℤ) = m₂ * ((n₁ : ℕ) : ℤ) := by
    simpa [mul_comm] using congrArg Neg.neg horderZ
  have hq : (m₁ : ℚ) / (↑n₁ : ℚ) = (m₂ : ℚ) / (↑n₂ : ℚ) := by
    rw [div_eq_div_iff (by exact_mod_cast n₁.ne_zero) (by exact_mod_cast n₂.ne_zero)]
    exact_mod_cast hint
  exact hq
/-- The empty set of height-one primes has polar density `0`, witnessed by the
constant continuation `F = fun _ => 1` with `n = 1` and `m = 0`. -/
@[simp] theorem hasPolarDensity_empty (K : Type*) [Field K] [NumberField K] :
  (∅ : Set (HeightOneSpectrum (𝓞 K))).HasPolarDensity 0 := by
  refine ⟨1, 0, fun _ => 1, MeromorphicAt.const (1 : ℂ) (1 : ℂ), ?_, ?_, ?_⟩
  · filter_upwards with z
    simp [NumberField.partialDedekindZeta_empty]
  · simpa using meromorphicOrderAt_const (𝕜 := ℂ) (1 : ℂ) (1 : ℂ)
  · simp

end NumberField.Set

/--
[hasPolarDensity_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PolarDensity.lean)
-/
@[path]
private lemma hasPolarDensity_empty_eq
  [Field K] [NumberField K] :
-- imply
  (∅ : Set (HeightOneSpectrum (𝓞 K))).HasPolarDensity 0 := by
-- proof
  apply NumberField.Set.hasPolarDensity_empty K


-- created on 2026-10-20
-- updated on 2026-10-26
