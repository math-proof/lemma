/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/KolmogorovMaximal.lean -/


import sympy.atlas.Probability.KolmogorovMaximal
import Lemma.Measure.KolmogorovMaximal


open Finset BigOperators

namespace MathlibExtTest.Probability.KolmogorovMaximal

/-- The maximal inequality applies to a concrete two-coin Rademacher model. -/
example :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin 2 → Bool =>
          ∃ i : Fin 2,
            |∑ j ∈ Finset.univ.filter
                (fun j : Fin 2 => j ≤ i),
              (if ω j then (1 : ℝ) else -1)| ≥ 2),
      ∏ i : Fin 2, (fun _ _ => (1 : ℝ) / 2) i (ω i))
    ≤ (∑ _i : Fin 2, ∑ _a : Bool, ((1 : ℝ) / 2) * (1 : ℝ) ^ 2) / 2 ^ 2 := by
  have h := MathlibExt.Probability.KolmogorovMaximal.kolmogorov_maximal_inequality
    (α := Bool) (n := 2)
    (p := fun _ _ => (1 : ℝ) / 2)
    (fun _ _ => by positivity)
    (fun _ => by
      have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [hu]
      norm_num)
    (X := fun _ a => if a then (1 : ℝ) else -1)
    (fun _ => by
      have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [hu]
      norm_num)
    (lam := 2) (by norm_num)
  simpa using h

/-- With identically zero variables the bad-event probability is zero for any `lam > 0`. -/
example (lam : ℝ) (hlam : 0 < lam) :
    (∑ _ω ∈ Finset.univ.filter
        (fun _ω : Fin 2 → Bool =>
          ∃ _i : Fin 2, |(0 : ℝ)| ≥ lam),
      ∏ _i : Fin 2, (1 : ℝ) / 2)
    ≤ (∑ _i : Fin 2, ∑ _a : Bool, ((1 : ℝ) / 2) * (0 : ℝ) ^ 2) / lam ^ 2 := by
  have h := MathlibExt.Probability.KolmogorovMaximal.kolmogorov_maximal_inequality
    (α := Bool) (n := 2)
    (p := fun _ _ => (1 : ℝ) / 2)
    (fun _ _ => by positivity)
    (fun _ => by
      have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [hu]
      norm_num)
    (X := fun _ _ => (0 : ℝ))
    (fun _ => by simp)
    (lam := lam) hlam
  simpa using h

/-- The general API restates with the exact public signature. -/
example {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (p : Fin n → α → ℝ)
    (hp_nonneg : ∀ i a, 0 ≤ p i a)
    (hp_sum : ∀ i, ∑ a : α, p i a = 1)
    (X : Fin n → α → ℝ)
    (h_mean : ∀ i, ∑ a : α, p i a * X i a = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin n → α =>
          ∃ i : Fin n,
            |∑ j ∈ Finset.univ.filter
                (fun j : Fin n => j ≤ i), X j (ω j)| ≥ lam),
      ∏ i : Fin n, p i (ω i))
    ≤ (∑ i : Fin n, ∑ a : α, p i a * (X i a) ^ 2) / lam ^ 2 :=
  MathlibExt.Probability.KolmogorovMaximal.kolmogorov_maximal_inequality
    p hp_nonneg hp_sum X h_mean lam hlam

end MathlibExtTest.Probability.KolmogorovMaximal
