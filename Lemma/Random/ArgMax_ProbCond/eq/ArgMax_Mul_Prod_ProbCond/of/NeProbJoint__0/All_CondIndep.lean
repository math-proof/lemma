import Lemma.Random.ProbCond.eq.DivMulProb_Prod_ProbCond.of.NeProbJoint__0.All_Indep
import Lemma.Random.Prob.ne.Zero.of.NeProb_0
import Macro.Order.ExprWithLimits
open MeasureTheory ProbabilityTheory Measure Random
open scoped ENNReal.ToRealCoe
open Fun
set_option maxHeartbeats 800000


/--
In NLP this is naive Bayes document classification (text categorization): given
bag-of-words features `x`, pick the class/label `yᵢ` that maximizes `ℙ(yᵢ | x)`,
rewritten as `ℙ(yᵢ) · ∏ⱼ ℙ(xⱼ | yᵢ)`.

Lemma binders use document features `y` and keywords/labels `x`. Under
conditional independence of each `y[t]` from its prefix `y[:t]` given the label
`x[i]`, and a nonzero joint,
`max⁻¹[i] ℙ(x[i] | y[:m]) =
 max⁻¹[i] (ℙ(x[i]) * ∏ j, ℙ(y[j] | x[i]))`
(the common factor `1 / ℙ(y[:m])` drops out of the argmax).

`[Fact (Measurable …)]` feeds `SinglePSpace π (x[:n], y[:m])` via the instance in
`sympy.stats.single_pspace_measurable`, so no explicit `hslice` binder is needed.
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
  {x : ℕ ⇀ Ω → α} {y : ℕ ⇀ Ω → β}
  {«x.bvar» : ℕ ⇀ α} [Fact (Measurable x[:n])]
  {«y.bvar» : ℕ ⇀ β} [Fact (Measurable y[:m])]
-- given
  (h₀ : ∀ (i : Fin n) (t : ℕ), 0 < t → t < m → y[t] ⟂ᵢ[π] y[:t] | x[i])
  (h₁ : ℙ[π](x[:n] = «x.bvar»[:n] ∧ y[:m] = «y.bvar»[:m]) ≠ 0) :
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
  max⁻¹[i : Fin n] (ℙ[π](x[i] = «x.bvar»[i] | y[:m] = «y.bvar»[:m]) : ℝ) =
    max⁻¹[i : Fin n] ((ℙ[π](x[i] = «x.bvar»[i]) : ℝ) * ∏ j : Fin m, (ℙ[π](y[j] = «y.bvar»[j] | x[i] = «x.bvar»[i]) : ℝ)) := by
-- proof
  intro hxi hyj hys hsp hxy hyx
  have h1i : ∀ i : Fin n, ℙ[π](x[i] = «x.bvar»[i] ∧ y[:m] = «y.bvar»[:m]) ≠ 0 := by
    intro i
    let xs : Ω → Fin n → α := x[:n]
    let ys : Ω → Fin m → β := y[:m]
    let z : Ω → (Fin n → α) × (Fin m → β) := (xs, ys)
    have hz : Measurable z :=
      Measurable.prodMk ‹Fact (Measurable x[:n])›.out ‹Fact (Measurable y[:m])›.out
    let g : (Fin n → α) × (Fin m → β) → α × (Fin m → β) :=
      fun p => (p.1 i, p.2)
    have hg : Measurable g :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    have hgz : g ∘ z = (x[i], show Ω → Fin m → β from y[:m]) := by
      funext ω
      rfl
    have hgv : g («x.bvar»[:n], «y.bvar»[:m]) = («x.bvar»[i], «y.bvar»[:m]) := rfl
    have h1z : π.prob z («x.bvar»[:n], «y.bvar»[:m]) ≠ 0 := h₁
    have : Fact (Measurable z) := ⟨hz⟩
    simpa [hgz, hgv] using Prob.ne.Zero.of.NeProb_0 (x := z) (g := g)
      («x.bvar»[:n], «y.bvar»[:m]) hg (h := h1z)
  have hMne : ℙ[π](y[:m] = «y.bvar»[:m]) ≠ 0 := by
    have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    have h1 := h1i i0
    let ys : Ω → Fin m → β := y[:m]
    let z : Ω → α × (Fin m → β) := (x[i0], ys)
    have hz : Measurable z :=
      Measurable.prodMk (hxi i0) ‹Fact (Measurable y[:m])›.out
    have hspz : SinglePSpace π z := hxy i0
    have h1z : π.prob z («x.bvar»[i0], «y.bvar»[:m]) ≠ 0 := h1
    have hsnd : Prod.snd ∘ z = y[:m] := by
      funext ω
      rfl
    have : Fact (Measurable z) := ⟨hz⟩
    simpa [hsnd] using Prob.ne.Zero.of.NeProb_0 (x := z) (g := Prod.snd)
      («x.bvar»[i0], «y.bvar»[:m]) measurable_snd (h := h1z)
  have hMtop : ℙ[π](y[:m] = «y.bvar»[:m]) ≠ ⊤ := by
    rw [Measure.prob,
      show (ReferenceMeasure.measure : Measure (Fin m → β)) = Measure.count from rfl,
      EqRnDeriv_Count]
    apply measure_ne_top
  have hc : 0 < (ℙ[π](y[:m] = «y.bvar»[:m]) : ℝ) :=
    ENNReal.toReal_pos hMne hMtop
  have hpt : ∀ i : Fin n,
      (ℙ[π](x[i] = «x.bvar»[i] | y[:m] = «y.bvar»[:m]) : ℝ) =
        ((ℙ[π](x[i] = «x.bvar»[i]) : ℝ) *
          ∏ j : Fin m, (ℙ[π](y[j] = «y.bvar»[j] | x[i] = «x.bvar»[i]) : ℝ)) /
        (ℙ[π](y[:m] = «y.bvar»[:m]) : ℝ) := by
    intro i
    have : Fact (Measurable x[i]) := ⟨hxi i⟩
    have hmul := ProbCond.eq.DivMulProb_Prod_ProbCond.of.NeProbJoint__0.All_Indep
      (x := x[i]) («x.bvar» := «x.bvar»[i])
      (y := y)
      (h₀ := fun t ht htm => h₀ i t ht htm)
      (h₁ := h1i i)
    simpa [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_prod] using
      congrArg ENNReal.toReal hmul
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
-- updated on 2026-10-23
