/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/WeakApproximation.lean -/

import Theorem.NumberTheory.NumberField.RayClass.WeakApproximation
import Lemma.Nat.NumberField.RayClass.WeakApproximation
@[expose] public noncomputable section

open scoped nonZeroDivisors
open NumberField


namespace N406WeakApproximationTest

variable {K : Type*} [Field K] [NumberField K]

-- Generic consumer: all-positive signs give strict positivity everywhere.
example (m : Modulus K) : ∃ x : K, x ≠ 0 ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Modulus.finiteSupported m v → v.valuation K x = 1) ∧
    ∀ w : RealPlace K, ∀ _hw : w ∈ m.infinitePart,
      0 < InfinitePlace.embedding_of_isReal w.property x := by
  classical
  obtain ⟨x, hxne, hval, hsign⟩ :=
    Modulus.exists_ne_zero_with_valuation_one_and_sign (K := K)
      m (fun _ : {w : RealPlace K // w ∈ m.infinitePart} => True)
  exact ⟨x, hxne, hval, fun w hw => (hsign w hw).1 trivial⟩

-- Empty modulus over `ℚ`: obligations rest on impossible membership.
example : ∃ x : ℚ, x ≠ 0 ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      Modulus.finiteSupported (1 : Modulus ℚ) v → v.valuation ℚ x = 1) ∧
    ∀ w : RealPlace ℚ, ∀ _hw : w ∈ (1 : Modulus ℚ).infinitePart,
      0 < InfinitePlace.embedding_of_isReal w.property x := by
  refine ⟨1, one_ne_zero, ?_, ?_⟩
  · intro v hv
    unfold Modulus.finiteSupported at hv
    rw [Modulus.one_finitePart] at hv
    have htop : v.asIdeal = ⊤ := top_le_iff.mp (by simpa using hv)
    exact (v.isPrime.ne_top htop).elim
  · intro w hw
    rw [Modulus.one_infinitePart] at hw
    exact (Finset.notMem_empty w hw).elim

-- Nontrivial sign predicate: both implication branches at a chosen place.
example (m : Modulus K) (w₀ : RealPlace K) (hw₀ : w₀ ∈ m.infinitePart)
    (pos : {w : RealPlace K // w ∈ m.infinitePart} → Prop) :
    ∃ x : K, x ≠ 0 ∧
      ((pos ⟨w₀, hw₀⟩ →
        0 < InfinitePlace.embedding_of_isReal w₀.property x) ∧
      (¬ pos ⟨w₀, hw₀⟩ →
        InfinitePlace.embedding_of_isReal w₀.property x < 0)) := by
  classical
  obtain ⟨x, hxne, _, hsign⟩ :=
    Modulus.exists_ne_zero_with_valuation_one_and_sign (K := K) m pos
  exact ⟨x, hxne, hsign w₀ hw₀⟩

-- Generic consumer of the finite-target theorem at chosen places.
example (m : Modulus K) (a : K) (ha0 : a ≠ 0)
    (haval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Modulus.finiteSupported m v → v.valuation K a = 1)
    (pos : {w : RealPlace K // w ∈ m.infinitePart} → Prop)
    (v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv₀ : Modulus.finiteSupported m v₀) (w₀ : RealPlace K)
    (hw₀ : w₀ ∈ m.infinitePart) :
    ∃ x : K, x ≠ 0 ∧ v₀.valuation K x = 1 ∧
      v₀.valuation K (x - a) ≤
        WithZero.exp (-(Modulus.finiteExponent m v₀)) ∧
      ((pos ⟨w₀, hw₀⟩ →
        0 < InfinitePlace.embedding_of_isReal w₀.property x) ∧
      (¬ pos ⟨w₀, hw₀⟩ →
        InfinitePlace.embedding_of_isReal w₀.property x < 0)) := by
  obtain ⟨x, hxne, hval, hsign⟩ :=
    Modulus.exists_ne_zero_with_target_and_sign m a pos ha0 haval
  obtain ⟨h1, h2⟩ := hval v₀ hv₀
  exact ⟨x, hxne, h1, h2, hsign w₀ hw₀⟩

-- The `a = 1` specialization recovers the old valuation-one-and-sign API.
example (m : Modulus K)
    (pos : {w : RealPlace K // w ∈ m.infinitePart} → Prop) :
    ∃ x : K, x ≠ 0 ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Modulus.finiteSupported m v → v.valuation K x = 1) ∧
      ∀ w : RealPlace K, ∀ hw : w ∈ m.infinitePart,
        (pos ⟨w, hw⟩ → 0 < InfinitePlace.embedding_of_isReal w.property x) ∧
        (¬ pos ⟨w, hw⟩ →
          InfinitePlace.embedding_of_isReal w.property x < 0) := by
  obtain ⟨x, hxne, hval, hsign⟩ :=
    Modulus.exists_ne_zero_with_target_and_sign m 1 pos one_ne_zero
      (fun _ _ => map_one _)
  exact ⟨x, hxne, fun v hv => (hval v hv).1, fun w hw => hsign w hw⟩

-- Unit-modulus edge case: vacuous finite obligations for arbitrary nonzero target.
example (a : ℚ) (ha0 : a ≠ 0)
    (pos : {w : RealPlace ℚ // w ∈ (1 : Modulus ℚ).infinitePart} → Prop) :
    ∃ x : ℚ, x ≠ 0 ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
        Modulus.finiteSupported (1 : Modulus ℚ) v →
          v.valuation ℚ x = 1 ∧
          v.valuation ℚ (x - a) ≤
            WithZero.exp (-(Modulus.finiteExponent (1 : Modulus ℚ) v))) ∧
      ∀ w : RealPlace ℚ, ∀ hw : w ∈ (1 : Modulus ℚ).infinitePart,
        (pos ⟨w, hw⟩ → 0 < InfinitePlace.embedding_of_isReal w.property x) ∧
        (¬ pos ⟨w, hw⟩ →
          InfinitePlace.embedding_of_isReal w.property x < 0) := by
  have haval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      Modulus.finiteSupported (1 : Modulus ℚ) v → v.valuation ℚ a = 1 := by
    intro v hv
    unfold Modulus.finiteSupported at hv
    rw [Modulus.one_finitePart] at hv
    have htop : v.asIdeal = ⊤ := top_le_iff.mp (by simpa using hv)
    exact (v.isPrime.ne_top htop).elim
  exact Modulus.exists_ne_zero_with_target_and_sign _ a pos ha0 haval

end N406WeakApproximationTest
