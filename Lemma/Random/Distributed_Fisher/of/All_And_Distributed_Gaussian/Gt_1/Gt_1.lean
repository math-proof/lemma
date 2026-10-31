import Mathlib.Probability.Distributions.Gaussian.Real
import Notation.Fun
import Notation.Probability.HasLaw
import Instance.Probability.Process.HiddenMarkovSequence
import Instance.NNReal.Coe
import Def.Probability.ChiSquare
import Def.Probability.Fisher
import Def.Probability.JointRv
import Lemma.Random.Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1
import Lemma.Random.Distributed_Fisher.of.Distributed_ChiSquared.Distributed_ChiSquared.Indep
import Lemma.Random.Distributed_ProdChiSquareS.of.All_And_Distributed_Gaussian.Gt_1.Gt_1
open MeasureTheory ProbabilityTheory Fun Random
open scoped NNReal


/--
One-way ANOVA F-statistic under H₀ (common mean).

Balanced design: m groups × n i.i.d. observations.
`S_B / σ² ∼ χ²(m - 1)` and `S_W / σ² ∼ χ²(m (n - 1))` independent, so their mean-square ratio is Fisher.

Between / within χ² margins:
[S_B / σ² ∼ χ²(m - 1)](?module=Random.Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1.sb),
[S_W / σ² ∼ χ²(m (n - 1))](?module=Random.Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1.sw).

Joint product (gives independence of the two χ²s):
[(S_B / σ², S_W / σ²) ∼ χ²(m − 1).prod χ²(m(n − 1))](?module=Random.Distributed_ProdChiSquareS.of.All_And_Distributed_Gaussian.Gt_1.Gt_1).

Independent χ² → Fisher:
[((X / d_x) / (Y / d_y)) ∼ fisherReal d_x d_y](?module=Random.Distributed_Fisher.of.Distributed_ChiSquared.Distributed_ChiSquared.Indep).

Algebraic identity [ST = S_B + S_W](?module=Finset.Sum_SquareSub_DivSum.eq.AddMul_Sum_SquareSubDivSSum).

All_And of Independence and Gaussian margins:
`∀ i j, y[i][:j] ⟂ᵢ[π] (y[:i, :j], y[i][j]) ∧ y[i][j] ∼[π] gaussianReal μ (σ : NNReal)²`
(`σ : ℝ⁺` cast to `NNReal` at the margin).
-/
@[path]
private lemma main
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
  ((((n : Ω → ℝ) *
        (∑ i : Fin m,
          ((∑ j : Fin n, y[i][j]) / (n : Ω → ℝ) -
              (∑ i : Fin m, ∑ j : Fin n, y[i][j]) / ((m * n : ℕ) : Ω → ℝ)) ^ 2)) /
      ((m - 1 : ℕ) : Ω → ℝ)) /
    ((∑ i : Fin m, ∑ j : Fin n,
      (y[i][j] -
        (∑ k : Fin n, y[i][k]) / (n : Ω → ℝ)) ^ 2) /
      ((m * (n - 1) : ℕ) : Ω → ℝ))) ∼[π]
    fisherReal (m - 1) (m * (n - 1)) := by
-- proof
  have : NeZero (m - 1) := ⟨ne_of_gt (Nat.sub_pos_of_lt hm)⟩
  have : NeZero (m * (n - 1)) :=
    ⟨ne_of_gt (Nat.mul_pos (Nat.zero_lt_of_lt hm) (Nat.sub_pos_of_lt hn))⟩
  let S_B :=
    (n : Ω → ℝ) *
      (∑ i : Fin m,
        ((∑ j : Fin n, y[i][j]) / (n : Ω → ℝ) -
            (∑ i : Fin m, ∑ j : Fin n, y[i][j]) / ((m * n : ℕ) : Ω → ℝ)) ^ 2)
  let S_W :=
    ∑ i : Fin m, ∑ j : Fin n,
      (y[i][j] -
        (∑ k : Fin n, y[i][k]) / (n : Ω → ℝ)) ^ 2
  let X := S_B / (σ² : Ω → ℝ)
  let Y := S_W / (σ² : Ω → ℝ)
  have hB : X ∼[π] Real.chiSquare (m - 1) := by
    simpa [X, S_B] using
      Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1.sb hm hn h
  have hW : Y ∼[π] Real.chiSquare (m * (n - 1)) := by
    simpa [Y, S_W] using
      Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1.sw hm hn h
  have hj : HasLaw (X, Y)
    ((Real.chiSquare (m - 1)).prod (Real.chiSquare (m * (n - 1)))) π := by
    simpa [X, Y, S_B, S_W] using
      Distributed_ProdChiSquareS.of.All_And_Distributed_Gaussian.Gt_1.Gt_1 hm hn h
  have hIndep : X ⟂ᵢ[π] Y :=
    (indepFun_iff_hasLaw_prodMk_prod hB hW).mpr <| by
      change HasLaw (X, Y) _ _
      exact hj
  have hF :=
    Distributed_Fisher.of.Distributed_ChiSquared.Distributed_ChiSquared.Indep
      hIndep hB hW
  have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt σ.property
  have heq :
    (S_B / ((m - 1 : ℕ) : Ω → ℝ)) / (S_W / ((m * (n - 1) : ℕ) : Ω → ℝ)) =
      (X / ((m - 1 : ℕ) : Ω → ℝ)) / (Y / ((m * (n - 1) : ℕ) : Ω → ℝ)) := by
    funext ω
    have hσ2 : (σ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hσ0
    simp only [X, Y, Pi.div_apply, Pi.natCast_apply]
    field_simp [hσ2]
  have hSBW :
    ((((n : Ω → ℝ) *
          (∑ i : Fin m,
            ((∑ j : Fin n, y[i][j]) / (n : Ω → ℝ) -
                (∑ i : Fin m, ∑ j : Fin n, y[i][j]) / ((m * n : ℕ) : Ω → ℝ)) ^ 2)) /
        ((m - 1 : ℕ) : Ω → ℝ)) /
      ((∑ i : Fin m, ∑ j : Fin n,
        (y[i][j] -
          (∑ k : Fin n, y[i][k]) / (n : Ω → ℝ)) ^ 2) /
        ((m * (n - 1) : ℕ) : Ω → ℝ))) =
        (S_B / ((m - 1 : ℕ) : Ω → ℝ)) / (S_W / ((m * (n - 1) : ℕ) : Ω → ℝ)) := by
    simp only [S_B, S_W]
  rw [hSBW, heq]
  apply hF


-- created on 2026-10-30
-- updated on 2026-10-31
