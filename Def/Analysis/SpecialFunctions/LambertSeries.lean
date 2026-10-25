/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/LambertSeries.lean -/

import Mathlib.Analysis.Complex.Basic


namespace MetaMathlibExt

/-!
# Lambert series from the Journal of Integer Sequences

Sources:

* Ž. Tomovski and S. Gerhold, *Mathieu-Fibonacci Series*, Journal of Integer Sequences 25
  (2022),
  [`gerhold6.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL25/Gerhold/gerhold6.tex).
* C. Vignat and M. Milgram, *Curious Multisection Identities by Index Factorization*,
  Journal of Integer Sequences 27 (2024),
  [`milgram5.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL27/Milgram/milgram5.tex).

All series are indexed by `k : ℕ`, with the papers' index `n = k + 1`.
-/

/-- The summand `qⁿ / (1 - qⁿ)` of the basic Lambert series. -/
noncomputable def lambertSeriesSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- The basic Lambert series `L(q) = ∑_{n≥1} qⁿ / (1 - qⁿ)`. -/
noncomputable def lambertSeries (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertSeriesSummand q k

/-- The summand `n qⁿ / (1 - qⁿ)` of the source's `f(q)`. -/
noncomputable def lambertFSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) * (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- The weighted Lambert series `f(q) = ∑_{n≥1} n qⁿ / (1 - qⁿ)`. -/
noncomputable def lambertF (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertFSummand q k

/-- The summand `n qⁿ / (1 + qⁿ)` of the source's `g(q)`. -/
noncomputable def lambertGSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) * (q : ℂ) ^ (k + 1) / (1 + (q : ℂ) ^ (k + 1))

/-- The weighted Lambert series `g(q) = ∑_{n≥1} n qⁿ / (1 + qⁿ)`. -/
noncomputable def lambertG (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertGSummand q k

/-- The summand `n^μ qⁿ / (1 - qⁿ)` of the source's `f_μ(q)`. -/
noncomputable def lambertFMuSummand (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) ^ (μ : ℕ) * (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- The power-weighted series `f_μ(q) = ∑_{n≥1} n^μ qⁿ / (1 - qⁿ)`. -/
noncomputable def lambertFMu (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) : ℂ :=
  ∑' k, lambertFMuSummand q μ k

/-- The summand `n^μ qⁿ / (1 + qⁿ)` of the source's `g_μ(q)`. -/
noncomputable def lambertGMuSummand (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) ^ (μ : ℕ) * (q : ℂ) ^ (k + 1) / (1 + (q : ℂ) ^ (k + 1))

/-- The power-weighted series `g_μ(q) = ∑_{n≥1} n^μ qⁿ / (1 + qⁿ)`. -/
noncomputable def lambertGMu (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) : ℂ :=
  ∑' k, lambertGMuSummand q μ k

/-- The summand `q^(mn) / (1 - q^(2n))^m` of the source's family `L_m(q)`. -/
noncomputable def lambertLmSummand (q : {q : ℂ // ‖q‖ < 1})
    (m : {m : ℕ // 1 ≤ m}) (k : ℕ) : ℂ :=
  (q : ℂ) ^ ((m : ℕ) * (k + 1)) /
    (1 - (q : ℂ) ^ (2 * (k + 1))) ^ (m : ℕ)

/-- The Lambert family `L_m(q) = ∑_{n≥1} q^(mn) / (1 - q^(2n))^m`. -/
noncomputable def lambertLm (q : {q : ℂ // ‖q‖ < 1})
    (m : {m : ℕ // 1 ≤ m}) : ℂ :=
  ∑' k, lambertLmSummand q m k

end MetaMathlibExt
