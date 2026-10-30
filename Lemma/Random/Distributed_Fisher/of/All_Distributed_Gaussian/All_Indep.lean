import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.BigOperators.Fin
import Notation.Fun
import Notation.Probability.HasLaw
import Notation.Algebra.Power
import Def.Probability.Fisher
import Lemma.Finset.Sum_SquareSub_DivSum.eq.AddMul_Sum_SquareSubDivSSum
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory
open Fun
open scoped NNReal



/--
One-way ANOVA F-statistic under H₀ (common mean).

Balanced design: `m` groups × `n` i.i.d. observations. Joint law of the grid is
taken as `Measure.pi` of `gaussianReal μ σ²` (i.i.d. normals; the 2D analogue of
the sequential `⟂ᵢ` hypotheses in `DistributedSum` / `ChiSquared` leaves).

Algebraic identity `ST = SB + SW` is
`Lemma.Finset.Sum_SquareSub_DivSum.eq.AddMul_Sum_SquareSubDivSSum`.
Under H₀ one has `SB / σ² ∼ χ²(m-1)`, `SW / σ² ∼ χ²(m(n-1))`, independent, hence
`F = (SB/(m-1)) / (SW/(m(n-1))) ∼ F(m-1, m(n-1))`, i.e. `fisherReal (m-1) (m*(n-1))`.

Per outcome `ω`:
* grand mean `μ̄ = (∑ᵢ ∑ⱼ y[i][j] ω) / (m * n)`
* row mean `ȳᵢ = (∑ⱼ y[i][j] ω) / n`
* `SB = n * ∑ᵢ (ȳᵢ - μ̄)²` (between / SSB)
* `SW = ∑ᵢ ∑ⱼ (y[i][j] ω - ȳᵢ)²` (within / SSW)
* `F = (SB / (m - 1)) / (SW / (m * (n - 1)))`

Requires `1 < m`, `1 < n` so both degrees of freedom are positive, and `0 < σ`
so the continuous law makes `SW = 0` a null event (σ cancels in `F`).
-/
@[path]
private lemma main
  {m n : ℕ}
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {y : ℕ ⇀ ℕ ⇀ Ω → ℝ}
  {μ : ℝ} {σ : NNReal}
-- given
  (hm : 1 < m)
  (hn : 1 < n)
  (hσ : 0 < (σ : ℝ))
  (h₀ : (fun ω (p : Fin m × Fin n) ↦ y[p.1.val][p.2.val] ω) ∼[π]
      Measure.pi fun _ : Fin m × Fin n ↦ gaussianReal μ σ²) :
-- imply
  (fun ω ↦
      let μbar :=
        (∑ i : Fin m, ∑ j : Fin n, y[i.val][j.val] ω) / (m * n : ℝ)
      let SB :=
        (n : ℝ) *
          ∑ i : Fin m,
            (((∑ j : Fin n, y[i.val][j.val] ω) / (n : ℝ) - μbar) ^ 2)
      let SW :=
        ∑ i : Fin m, ∑ j : Fin n,
          (y[i.val][j.val] ω -
              (∑ k : Fin n, y[i.val][k.val] ω) / (n : ℝ)) ^ 2
      (SB / (m - 1 : ℝ)) / (SW / ((m * (n - 1) : ℕ) : ℝ))) ∼[π]
    fisherReal (m - 1) (m * (n - 1)) := by
-- proof
  -- Intermediate: for each ω, Finset gives ST = SB + SW on the realized grid
  -- `⟨fun i ↦ ⟨fun j ↦ y[i][j] ω⟩⟩`. Then SB/σ² ∼ χ²(m-1), SW/σ² ∼ χ²(m(n-1))
  -- independent under H₀, so F ∼ fisherReal (m-1) (m*(n-1)).
  have _hST :=
    fun ω ↦ Finset.Sum_SquareSub_DivSum.eq.AddMul_Sum_SquareSubDivSSum
      (R := ℝ) (m := m) (n := n) (x := ⟨fun i ↦ ⟨fun j ↦ y[i][j] ω⟩⟩)
  sorry


-- created on 2026-10-30
-- updated on 2026-10-30
