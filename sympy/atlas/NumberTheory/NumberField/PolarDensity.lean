/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PolarDensity.lean -/

import sympy.atlas.NumberTheory.NumberField.PartialDedekindZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Polar density of sets of height-one primes

This module introduces the corrected polar-density API for `ATLAS NumberTheoryI N409`.

The key semantic correction: `MeromorphicAt` is asserted of `F`, the actual
meromorphic continuation, never of the raw Euler-product `tprod`.
The raw Euler product is only used as a pointwise germ on the right half-plane
`{z : ℂ | 1 < z.re}` near `1`.
-/

open Filter Topology NumberField IsDedekindDomain

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

/-- Polar density of a set of height-one primes, via a meromorphic continuation.

`HasPolarDensity S ρ` asserts the existence of a positive exponent `n : ℕ+`, a
pole order `m : ℤ`, and an actual meromorphic continuation `F : ℂ → ℂ` such that
`F` is meromorphic at `1`, agrees with the pointwise `n`-th power of the partial
Dedekind zeta function on the right-half-plane germ at `1`, has
`meromorphicOrderAt F 1 = -m`, and `ρ = m / n`. -/
def HasPolarDensity (S : Set (HeightOneSpectrum (𝓞 K))) (ρ : ℚ) : Prop :=
  ∃ (n : ℕ+) (m : ℤ) (F : ℂ → ℂ),
    MeromorphicAt F (1 : ℂ) ∧
      F =ᶠ[nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}]
        (fun s => NumberField.partialDedekindZeta K S s ^ (n : ℕ)) ∧
      meromorphicOrderAt F (1 : ℂ) = (↑(-m) : WithTop ℤ) ∧
      ρ = (m : ℚ) / (n : ℚ)

private theorem eventuallyEq_nhdsNE_of_eventuallyEq_re_gt_one
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

/-- Uniqueness of the polar density: the `NeBot`/closure argument above is
essential, without it side equality could be vacuous. -/
theorem HasPolarDensity.unique {S : Set (HeightOneSpectrum (𝓞 K))} {ρ₁ ρ₂ : ℚ}
    (h₁ : S.HasPolarDensity ρ₁) (h₂ : S.HasPolarDensity ρ₂) : ρ₁ = ρ₂ := by
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
