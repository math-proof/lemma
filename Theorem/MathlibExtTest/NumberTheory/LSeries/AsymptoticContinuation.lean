/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AsymptoticContinuation.lean -/


import Def.NumberTheory.LSeries.AsymptoticContinuation
import Lemma.Nat.LSeries.AsymptoticContinuation
open Filter Asymptotics Topology


/-- Constant coefficients: the remainder continuation vanishes, leaving
the normalized pole part `ρ * riemannZeta`. -/
example (ρ s : ℂ) :
    linearAsymptoticDirichletContinuation (fun _ => ρ) ρ s =
      ρ * riemannZeta s := by
  have hfun : (fun n => (fun _ : ℕ => ρ) n - ρ) = fun _ => (0 : ℂ) := by
    funext n
    simp
  have hzero : abelContinuation (fun n => (fun _ : ℕ => ρ) n - ρ) s = 0 := by
    rw [hfun]
    simp [abelContinuation, abelSummatory, abelPartialSum]
  unfold linearAsymptoticDirichletContinuation
  rw [hzero, add_zero]

/-- Closed `ρ = 1`, `σ = 0` residue limit on the constant sequence. -/
example :
    Tendsto
      (fun s : ℂ =>
        (s - 1) * linearAsymptoticDirichletContinuation (fun _ => 1) 1 s)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
  tendsto_sub_one_mul_linearAsymptoticDirichletContinuation _ _
    (zero_lt_one : (0 : ℝ) < 1) (isBigO_const_remainder 1)

/-- Closed `ρ = 1`, `σ = 0` order `-1` example on the constant sequence. -/
example :
    meromorphicOrderAt
      (linearAsymptoticDirichletContinuation (fun _ => 1) 1) 1 =
      ((-1 : ℤ) : WithTop ℤ) :=
  meromorphicOrderAt_linearAsymptoticDirichletContinuation_one _ _
    (zero_lt_one : (0 : ℝ) < 1) (isBigO_const_remainder 1) one_ne_zero

variable (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ}
  (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
    fun n => ((n : ℝ) ^ σ : ℝ))

include hO

/-- Analyticity away from `1` delegates to production. -/
example {s : ℂ} (hs : σ < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (linearAsymptoticDirichletContinuation a ρ) s :=
  analyticAt_linearAsymptoticDirichletContinuation_of_ne_one a ρ hO hs hs1

/-- Meromorphicity on the half-plane delegates to production. -/
example (hσ1 : σ < 1) :
    MeromorphicOn (linearAsymptoticDirichletContinuation a ρ)
      {s : ℂ | σ < s.re} :=
  meromorphicOn_linearAsymptoticDirichletContinuation a ρ hσ1 hO

/-- Residue limit delegates to production. -/
example (hσ1 : σ < 1) :
    Tendsto (fun s : ℂ => (s - 1) * linearAsymptoticDirichletContinuation a ρ s)
      (𝓝[≠] (1 : ℂ)) (𝓝 ρ) :=
  tendsto_sub_one_mul_linearAsymptoticDirichletContinuation a ρ hσ1 hO

/-- Order at `1` delegates to production. -/
example (hσ1 : σ < 1) (hρ : ρ ≠ 0) :
    meromorphicOrderAt (linearAsymptoticDirichletContinuation a ρ) 1 =
      ((-1 : ℤ) : WithTop ℤ) :=
  meromorphicOrderAt_linearAsymptoticDirichletContinuation_one a ρ hσ1 hO hρ

/-- Icc partial sums converge to the continuation delegates to production. -/
example (hσ1 : σ < 1) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term a s n) atTop
      (𝓝 (linearAsymptoticDirichletContinuation a ρ s)) :=
  tendsto_linearAsymptoticDirichletContinuation_Icc a ρ hσ1 hO hs

