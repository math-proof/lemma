import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Probability.NumberTheory.RandomMultiplicativeFunction.Part2
open MeasureTheory ProbabilityTheory ArithmeticFunction
open scoped ENNReal
open MetaMathlibExt.RandomMultiplicativeFunction


namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[rademacherMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma rademacherMeasure_singleton
  {x : ℤˣ} :
-- imply
  rademacherMeasure {x} = (2 : ENNReal)⁻¹ := by
-- proof
  have hs : MeasurableSet ({x} : Set ℤˣ) := by
    have h_coe : Measurable (fun u : ℤˣ => (u : ℤ)) :=
      measurable_iff_comap_le.2 le_rfl
    have h_eq : ({x} : Set ℤˣ) =
      (fun u : ℤˣ => (u : ℤ)) ⁻¹' ({(x : ℤ)} : Set ℤ) := by
      ext u
      simp [Units.ext_iff]
    rw [h_eq]
    exact h_coe (measurableSet_singleton _)
  rw [rademacherMeasure, PMF.toMeasure_uniformOfFintype_apply _ hs]
  simp [Fintype.card_units_int]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[exists_rademacherFamily](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma exists_rademacherFamily
  :
-- imply
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : Nat.Primes → Ω → ℤˣ),
    IsRademacherFamily μ X ∧ IsProbabilityMeasure μ := by
-- proof
  obtain ⟨Ω, hM, μ, X, hMeas, hLaw, hIndep, hProb⟩ :=
    exists_iid Nat.Primes rademacherMeasure
  exact ⟨Ω, hM, μ, X, ⟨hMeas, hLaw, hIndep⟩, hProb⟩

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[primeSignNat_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma primeSignNat_prime
  {X : Nat.Primes → Ω → ℤˣ}
  {p : ℕ}
  {ω : Ω}
-- given
  (hp : Nat.Prime p) :
-- imply
  primeSignNat X p ω = (X ⟨p, hp⟩ ω : ℤ) := by
-- proof
  simp [primeSignNat, hp]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[primeSignNat_not_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma primeSignNat_not_prime
  {X : Nat.Primes → Ω → ℤˣ}
  {n : ℕ}
  {ω : Ω}
-- given
  (hn : ¬Nat.Prime n) :
-- imply
  primeSignNat X n ω = 1 := by
-- proof
  simp [primeSignNat, hn]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[IsRademacherFamily.measurable_primeSignNat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma IsRademacherFamily.measurable_primeSignNat
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Nat.Primes → Ω → ℤˣ}
  {n : ℕ}
-- given
  (hX : IsRademacherFamily μ X) :
-- imply
  Measurable (primeSignNat X n) := by
-- proof
  by_cases hn : Nat.Prime n
  · have h_coe : Measurable (fun u : ℤˣ => (u : ℤ)) :=
    measurable_iff_comap_le.2 le_rfl
    have h_eq : primeSignNat X n = fun ω => (X ⟨n, hn⟩ ω : ℤ) := by
      funext ω
      exact primeSignNat_prime hn
    rw [h_eq]
    exact h_coe.comp (hX.1 ⟨n, hn⟩)
  · have h_eq : primeSignNat X n = fun _ => 1 := by
    funext ω
    exact primeSignNat_not_prime hn
    rwa [h_eq]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[rademacherFunction_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma rademacherFunction_apply
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  rademacherFunction X ω n =
    ((moebius n : ℤ) ^ 2) * ∏ p ∈ n.primeFactors, primeSignNat X p ω := by
-- proof
  simp [rademacherFunction, pmul_apply, prodPrimeFactors_apply hn, pow_two]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[rademacherFunction_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma rademacherFunction_one
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω} :
-- imply
  rademacherFunction X ω 1 = 1 := by
-- proof
  have h1 : (1 : ℕ) ≠ 0 := by decide
  simp [rademacherFunction_apply h1]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[rademacherFunction_eq_prod_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma rademacherFunction_eq_prod_of_squarefree
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {n : ℕ}
-- given
  (hn : Squarefree n) :
-- imply
  rademacherFunction X ω n = ∏ p ∈ n.primeFactors, primeSignNat X p ω := by
-- proof
  rw [rademacherFunction_apply hn.ne_zero, moebius_sq_eq_one_of_squarefree hn, one_mul]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[rademacherFunction_eq_zero_of_not_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma rademacherFunction_eq_zero_of_not_squarefree
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {n : ℕ}
-- given
  (hn : ¬Squarefree n) :
-- imply
  rademacherFunction X ω n = 0 := by
-- proof
  by_cases hn0 : n = 0
  · simp [hn0]
  · simp [rademacherFunction_apply hn0, moebius_eq_zero_of_not_squarefree hn]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[isMultiplicative_rademacherFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma isMultiplicative_rademacherFunction
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω} :
-- imply
  IsMultiplicative (rademacherFunction X ω) :=
-- proof
  (isMultiplicative_moebius.pmul isMultiplicative_moebius).pmul
    (IsMultiplicative.prodPrimeFactors _)

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[rademacherFunction_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma rademacherFunction_prime
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  rademacherFunction X ω p = primeSignNat X p ω := by
-- proof
  have hpf : p.primeFactors = {p} := by
    simpa using Nat.primeFactors_prime_pow (p := p) (k := 1) (by decide) hp
  rw [rademacherFunction_eq_prod_of_squarefree hp.squarefree, hpf, Finset.prod_singleton]

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[rademacherFunction_prime_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma rademacherFunction_prime_sq
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  rademacherFunction X ω (p ^ 2) = 0 := by
-- proof
  apply rademacherFunction_eq_zero_of_not_squarefree
  rw [Nat.squarefree_pow_iff hp.ne_one (by decide : 2 ≠ 0)]
  simp

end MetaMathlibExt.RandomMultiplicativeFunction

namespace MetaMathlibExt.RandomMultiplicativeFunction

/--
[IsRademacherFamily.measurable_rademacherFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
lemma IsRademacherFamily.measurable_rademacherFunction
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Nat.Primes → Ω → ℤˣ}
  {n : ℕ}
-- given
  (hX : IsRademacherFamily μ X) :
-- imply
  Measurable (fun ω => rademacherFunction X ω n) := by
-- proof
  by_cases hn : n = 0
  · subst n
    have h_eq : (fun ω => rademacherFunction X ω 0) = fun _ => (0 : ℤ) := by
      funext ω
      simp
    rwa [h_eq]
  · have hprod : Measurable (fun ω => ∏ p ∈ n.primeFactors, primeSignNat X p ω) :=
    Finset.measurable_prod n.primeFactors fun p _ => hX.measurable_primeSignNat p
    have h_eq : (fun ω => rademacherFunction X ω n) =
      fun ω => ((moebius n : ℤ) ^ 2) * ∏ p ∈ n.primeFactors, primeSignNat X p ω := by
      funext ω
      exact rademacherFunction_apply hn
    rw [h_eq]
    exact measurable_const.mul hprod

end MetaMathlibExt.RandomMultiplicativeFunction


-- created on 2026-10-20
-- updated on 2026-10-26
