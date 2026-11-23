import Lemma.Random.ProbCond.eq.DivMulProb_Prod_ProbCond.of.NeProbJoint__0.All_Indep
import Syntax.Order.ExprWithLimits
import Notation.Probability.JointRv
import Initialize.Tactic.Attr.Basic
import Instance.Data.Nat.Fun
open MeasureTheory ProbabilityTheory Measure Random
open scoped ENNReal.ToRealCoe
open Fun
set_option maxHeartbeats 800000


/--
Let \(x\) and \(y\) be the sets of words used as vocabularies on the documents \(X\) and \(Y\) sides, respectively.

Let \(N\) be the number of corpus pairs and let \(k\) index those pairs.
Each pair is \((X_k,Y_k)\). Each \(X_k\) is represented
by a subset of \(x\), and each \(Y_k\) by a subset of \(y\).
Write \(x_i\) and \(y_j\) for the indexed words in the two vocabularies.
Encode each membership event as a binary feature and let \(\pi\) give each
of the \(N\) corpus pairs weight \(1/N\). Let \(\mathcal{X}\) and \(\mathcal{Y}\) denote the documents in the randomly
selected pair. If the selected index is \(k\), then
\((\mathcal{X},\mathcal{Y})=(X_k,Y_k)\). The joint and marginal probabilities
are

\[
\begin{aligned}
\mathbb P_\pi(y_j\in\mathcal{Y} \land x_i\in\mathcal{X})
  &= \frac{\left|\{k : x_i\in X_k \land y_j\in Y_k\}\right|}{N}, \\
\mathbb P_\pi(x_i\in\mathcal{X})
  &= \frac{\left|\{k : x_i\in X_k\}\right|}{N}.
\end{aligned}
\]

If \(\mathbb P_\pi(x_i\in\mathcal{X})>0\), the
[conditional probability quotient](?lemma=Random.All_EqProb_Cond__DivProbS.of.SinglePSpace)
gives the empirical **conditional co-occurrence probability** (条件共现概率)

\[
\begin{aligned}
\widehat{\mathbb P}_\pi(y_j\in\mathcal{Y}\mid x_i\in\mathcal{X})
  &= \frac{\mathbb P_\pi(y_j\in\mathcal{Y} \land x_i\in\mathcal{X})}
          {\mathbb P_\pi(x_i\in\mathcal{X})} \\
  &= \frac{\left|\{k : x_i\in X_k \land y_j\in Y_k\}\right|/N}
          {\left|\{k : x_i\in X_k\}\right|/N} \\
  &= \frac{\left|\{k : x_i\in X_k \land y_j\in Y_k\}\right|}
          {\left|\{k : x_i\in X_k\}\right|}.
\end{aligned}
\]

# multi-label document classification
Suppose you have a document consisting of subset of \(y\), and \(Y\) is labeled with some semantic tags (subset of \(x\));
Now that there is a corpus consisting of pairs of document and its respective set of semantic tags;
You are then given a new document \(Y'\), how to figure out the way of choosing the semantic tags (subset of \(x\)) with optimal probability?

# X-cited patent examination
Another application is predicting words in an X-cited reference. In this corpus, \(Y_k\) is the application under examination and \(X_k\) is a document cited as category X against a claim of \(Y_k\).
For a new application \(Y′\), use its observed words as evidence. Under the lemma's assumptions, rank each candidate word for a counterpart \(X′\) by its frequency of occurrence on the \(X\) side times the product of the observed \(Y′\) word likelihoods conditioned on that candidate word being present.
The highest-scoring words can help retrieve candidate references. A retrieved \(X′\) is an X-cited document for \(Y′\) if the search report cites it as category X against a claim of \(Y′\).
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure α] [CountableMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [NeZero (n : ℕ)]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m : ℕ}
  {x : ℕ → Ω → α} {y : ℕ → Ω → β}
  {«\sf{x}» : ℕ → α} [Fact (Measurable x[:n])]
  {«\sf{y}» : ℕ → β} [Fact (Measurable y[:m])]
-- given
  (h₀ : ∀ (i : Fin n) (t : ℕ), 0 < t → t < m → y[t] ⟂ᵢ[π] y[:t] | x[i]) :
-- imply
  have : ∀ i : Fin n, Measurable x[i] :=
    fun i => (measurable_pi_apply i).comp ‹Fact (Measurable x[:n])›.out
  have : ∀ j : Fin m, Measurable y[j] :=
    fun j => (measurable_pi_apply j).comp ‹Fact (Measurable y[:m])›.out
  have : SinglePSpace π y[:m] :=
    SinglePSpace.of.Measurable ‹Fact (Measurable y[:m])›.out
  have : ∀ i : Fin n, SinglePSpace π (x i) :=
    fun i => SinglePSpace.of.Measurable
      ((measurable_pi_apply i).comp ‹Fact (Measurable x[:n])›.out)
  have : ∀ i : Fin n, SinglePSpace π (x[i], show Ω → Fin m → β from y[:m]) :=
    fun i => SinglePSpace.of.Measurable.Measurable
      ((measurable_pi_apply i).comp ‹Fact (Measurable x[:n])›.out)
      ‹Fact (Measurable y[:m])›.out
  have : ∀ (i : Fin n) (j : Fin m), SinglePSpace π (y[j], x[i]) :=
    fun i j => SinglePSpace.of.Measurable.Measurable
      ((measurable_pi_apply j).comp ‹Fact (Measurable y[:m])›.out)
      ((measurable_pi_apply i).comp ‹Fact (Measurable x[:n])›.out)
  max⁻¹[i : Fin n] (ℙ[π](x[i] = «\sf{x}»[i] | y[:m] = «\sf{y}»[:m]) : ℝ) =
    max⁻¹[i : Fin n] (ℙ[π](x[i] = «\sf{x}»[i]) : ℝ) * (∏ j : Fin m, (ℙ[π](y[j] = «\sf{y}»[j] | x[i] = «\sf{x}»[i]) : ℝ)) := by
-- proof
  intro hxi hyj hys hsp hxy hyx
  let evidence := ℙ[π](y[:m] = «\sf{y}»[:m])
  have hevidenceTop : evidence ≠ ⊤ := by
    dsimp only [evidence]
    rw [Measure.prob,
      show ReferenceMeasure.measure = Measure.count from rfl,
      EqRnDeriv_Count]
    apply measure_ne_top
  -- Zero evidence gives zero scores on both sides, so use a positive scale there.
  let scale : ℝ := if evidence = 0 then 1 else evidence.toReal
  have hc : 0 < scale := by
    dsimp only [scale]
    split
    · norm_num
    · exact ENNReal.toReal_pos (by assumption) hevidenceTop
  have hpt : ∀ i : Fin n,
      (ℙ[π](x[i] = «\sf{x}»[i] | y[:m] = «\sf{y}»[:m]) : ℝ) =
        (ℙ[π](x[i] = «\sf{x}»[i]) : ℝ) *
          (∏ j : Fin m, (ℙ[π](y[j] = «\sf{y}»[j] | x[i] = «\sf{x}»[i]) : ℝ)) /
        scale := by
    intro i
    have : Fact (Measurable x[i]) := ⟨hxi i⟩
    have hmul := ProbCond.eq.DivMulProb_Prod_ProbCond.of.NeProbJoint__0.All_Indep
      (x := x[i]) («\sf{x}» := «\sf{x}»[i])
      (y := y) («\sf{y}» := «\sf{y}»)
      (h₀ := fun t ht htm => h₀ i t ht htm)
    if he : evidence = 0 then
      have hmeasure : π ((show Ω → Fin m → β from y[:m]) ⁻¹' {«\sf{y}»[:m]}) = 0 :=
        (EqProb (x := (show Ω → Fin m → β from y[:m])) _).symm.trans he
      have hjoint := measure_mono_null
        (Set.inter_subset_right (s := x[i] ⁻¹' {«\sf{x}»[i]})) hmeasure
      have hzero : ℙ[π](x[i] = «\sf{x}»[i] | y[:m] = «\sf{y}»[:m]) = 0 := by
        rw [Prob_Cond.eq.Div.of.SinglePSpace (hxy i), hjoint, ENNReal.zero_div]
      dsimp only at hmul
      rw [hzero, show ℙ[π](y[:m] = «\sf{y}»[:m]) = 0 from he] at hmul
      have hn := hmul.symm
      simp only [div_eq_mul_inv, ENNReal.inv_zero, mul_eq_zero, ENNReal.top_ne_zero, or_false] at hn
      dsimp only [scale]
      simp only [he, ite_true, div_one]
      rw [hzero, ENNReal.toReal_zero, zero_eq_mul]
      rcases hn with h | h
      · left
        rw [h, ENNReal.toReal_zero]
      · right
        rw [← ENNReal.toReal_prod, h, ENNReal.toReal_zero]
    else
      simpa [scale, he, evidence, ENNReal.toReal_div, ENNReal.toReal_mul,
        ENNReal.toReal_prod] using congrArg ENNReal.toReal hmul
  unfold «max⁻¹»
  congr 1
  funext i
  apply propext
  constructor
  ·
    rintro ⟨hi, hle⟩
    refine ⟨hi, fun j hj => ?_⟩
    have hfj := hpt j
    have hfi := hpt i
    have hlej := hle j hj
    beta_reduce at hlej
    rw [hfj, hfi] at hlej
    apply (div_le_div_iff_of_pos_right hc).mp hlej
  ·
    rintro ⟨hi, hle⟩
    refine ⟨hi, fun j hj => ?_⟩
    have hfj := hpt j
    have hfi := hpt i
    have hlej := hle j hj
    beta_reduce
    rw [hfj, hfi]
    apply (div_le_div_iff_of_pos_right hc).mpr hlej


-- created on 2021-07-21
-- updated on 2026-11-23
