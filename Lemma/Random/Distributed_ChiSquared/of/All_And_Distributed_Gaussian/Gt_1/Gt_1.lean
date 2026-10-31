import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Notation.Fun
import Notation.Probability.HasLaw
import Instance.Probability.Process.HiddenMarkovSequence
import Instance.NNReal.Coe
import Def.Probability.ChiSquare
import Lemma.Random.Distributed_ProdChiSquareS.of.All_And_Distributed_Gaussian.Gt_1.Gt_1
open MeasureTheory ProbabilityTheory Fun Measure
open scoped NNReal
set_option maxHeartbeats 800000


/--
Between-group sum of squares under H₀ (common mean).

Balanced design: m groups × n i.i.d. observations.
`S_B / σ² ∼ χ²(m - 1)`.

Joint product law:
[(S_B / σ², S_W / σ²) ∼ χ²(m − 1).prod χ²(m(n − 1))](?module=Random.Distributed_ProdChiSquareS.of.All_And_Distributed_Gaussian.Gt_1.Gt_1).

Sibling within-group law:
[S_W / σ² ∼ χ²(m (n - 1))](?module=Random.Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1.sw).

ANOVA F under the same hyps:
[F ∼ fisherReal (m - 1) (m (n - 1))](?module=Random.Distributed_Fisher.of.All_And_Distributed_Gaussian.Gt_1.Gt_1).

All_And of Independence and Gaussian margins:
`∀ i j, y[i][:j] ⟂ᵢ[π] (y[:i, :j], y[i][j]) ∧ y[i][j] ∼[π] gaussianReal μ (σ : NNReal)²`
(`σ : ℝ⁺` cast to `NNReal` at the margin).
-/
@[path]
private lemma sb
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m n : ℕ}
  {y : ℕ ⇀ ℕ ⇀ Ω → ℝ}
  {μ : ℝ} {σ : ℝ⁺}
-- given
  (hm : m > 1)
  (hn : n > 1)
  (h : ∀ (i j : ℕ), y[i][:j] ⟂ᵢ[π]
        ((y[:i, :j] : Ω → Fin i → Fin j → ℝ), y[i][j]) ∧
      y[i][j] ∼[π] gaussianReal μ (σ : NNReal)²) :
-- imply
  ((n : Ω → ℝ) *
      (∑ i : Fin m,
        ((∑ j : Fin n, y[i][j]) / (n : Ω → ℝ) -
            (∑ i : Fin m, ∑ j : Fin n, y[i][j]) / ((m * n : ℕ) : Ω → ℝ)) ^ 2)) /
    (σ² : Ω → ℝ) ∼[π]
      Real.chiSquare (m - 1) := by
-- proof
  have : NeZero (m - 1) := ⟨ne_of_gt (Nat.sub_pos_of_lt hm)⟩
  have : NeZero (m * (n - 1)) :=
    ⟨ne_of_gt (Nat.mul_pos (Nat.zero_lt_of_lt hm) (Nat.sub_pos_of_lt hn))⟩
  have hj := Random.Distributed_ProdChiSquareS.of.All_And_Distributed_Gaussian.Gt_1.Gt_1 hm hn h
  have hfst : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (Real.chiSquare (m - 1))
    ((Real.chiSquare (m - 1)).prod (Real.chiSquare (m * (n - 1)))) :=
    ⟨measurable_fst.aemeasurable, by
      simp⟩
  exact hfst.fun_comp hj


/--
Within-group sum of squares under H₀ (common mean).

Balanced design: m groups × n i.i.d. observations.
`S_W / σ² ∼ χ²(m (n - 1))`.

Sibling between-group law:
[S_B / σ² ∼ χ²(m - 1)](?module=Random.Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1.sb).

ANOVA F under the same hyps:
[F ∼ fisherReal (m - 1) (m (n - 1))](?module=Random.Distributed_Fisher.of.All_And_Distributed_Gaussian.Gt_1.Gt_1).

All_And of Independence and Gaussian margins:
`∀ i j, y[i][:j] ⟂ᵢ[π] (y[:i, :j], y[i][j]) ∧ y[i][j] ∼[π] gaussianReal μ (σ : NNReal)²`
(`σ : ℝ⁺` cast to `NNReal` at the margin).
-/
@[path]
private lemma sw
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m n : ℕ}
  {y : ℕ ⇀ ℕ ⇀ Ω → ℝ}
  {μ : ℝ} {σ : ℝ⁺}
-- given
  (hm : m > 1)
  (hn : n > 1)
  (h : ∀ (i j : ℕ), y[i][:j] ⟂ᵢ[π]
        ((y[:i, :j] : Ω → Fin i → Fin j → ℝ), y[i][j]) ∧
      y[i][j] ∼[π] gaussianReal μ (σ : NNReal)²) :
-- imply
  (∑ i : Fin m, ∑ j : Fin n,
      (y[i][j] -
        (∑ k : Fin n, y[i][k]) / (n : Ω → ℝ)) ^ 2) /
    (σ² : Ω → ℝ) ∼[π]
      Real.chiSquare (m * (n - 1)) := by
-- proof
  have : NeZero (m - 1) := ⟨ne_of_gt (Nat.sub_pos_of_lt hm)⟩
  have : NeZero (m * (n - 1)) :=
    ⟨ne_of_gt (Nat.mul_pos (Nat.zero_lt_of_lt hm) (Nat.sub_pos_of_lt hn))⟩
  have hj := Random.Distributed_ProdChiSquareS.of.All_And_Distributed_Gaussian.Gt_1.Gt_1 hm hn h
  have hsnd : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (Real.chiSquare (m * (n - 1)))
    ((Real.chiSquare (m - 1)).prod (Real.chiSquare (m * (n - 1)))) :=
    ⟨measurable_snd.aemeasurable, by
      simp⟩
  exact hsnd.fun_comp hj


-- created on 2026-10-30
-- updated on 2026-10-31
