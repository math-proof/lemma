import Instance.Analysis.Real.Numbers
import Instance.Probability.SinglePSpaceMeasurable
import Theorem.Probability.CondExpectation
import Theorem.Probability.JointRv.AsRV
import Lemma.Random.Prob_Cond.eq.Div.of.SinglePSpace
open MeasureTheory ProbabilityTheory Random
open scoped ENNReal.ToRealCoe


/--
Conditional importance sampling for one pair of random variables, with no time index.
At each observation `s = «\sf{s}»`,
`𝔼[x : π](f x | s = «\sf{s}»)` equals
`𝔼[x : π'](((ℙ[π](x | s = «\sf{s}») / ℙ[π'](x | s = «\sf{s}»)) : ℝ) • f x | s = «\sf{s}»)`.
The target joint vanishes wherever the proposal joint does.

Unconditional form:
[importance sampling](?module=Random.Expect.eq.Expect_SMulDivProbS.of.All_ImpEqSProb__0.Measurable).
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [CountableMeasure α] [Fintype α] [Nonempty α] [StandardBorelSpace α] [MeasurableSingletonClass α]
  [CountableMeasure β] [Countable β] [MeasurableSingletonClass β]
  {π π' : Measure Ω} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
  {x : Ω → α} [Fact (Measurable x)]
  {s : Ω → β} [Fact (Measurable s)]
  {f : α → E}
-- given
  (h₀ : ∀ «\sf{x}» «\sf{s}»,
    ℙ[π'](x = «\sf{x}» ∧ s = «\sf{s}») = 0 →
      ℙ[π](x = «\sf{x}» ∧ s = «\sf{s}») = 0) :
-- imply
  ∀ «\sf{s}», π.map s {«\sf{s}»} ≠ 0 →
    𝔼[x : π](f x | s = «\sf{s}») =
      𝔼[x : π'](((ℙ[π](x | s = «\sf{s}») / ℙ[π'](x | s = «\sf{s}»)) : ℝ) • f x | s = «\sf{s}») := by
-- proof
  intro «\sf{s}» hpos
  have hx : Measurable x := ‹Fact (Measurable x)›.out
  have hs : Measurable s := ‹Fact (Measurable s)›.out
  have hJoint (φ : Measure Ω) [IsProbabilityMeasure φ] [SinglePSpace φ (x, s)]
    («\sf{x}» : α) («\sf{s}» : β) :
      ℙ[φ](x = «\sf{x}» ∧ s = «\sf{s}») = φ (x ⁻¹' {«\sf{x}»} ∩ s ⁻¹' {«\sf{s}»}) := by
    rw [_root_.Random.EqProb]
    congr 1
    ext ω
    simp [JointRandomSymbol, Prod.ext_iff]
  have hpos' : π'.map s {«\sf{s}»} ≠ 0 := by
    intro h'0
    have hs0' : π' (s ⁻¹' {«\sf{s}»}) = 0 :=
      (Measure.map_apply hs (measurableSet_singleton «\sf{s}»)).symm.trans h'0
    have hjs' («\sf{x}» : α) : ℙ[π'](x = «\sf{x}» ∧ s = «\sf{s}») = 0 := by
      rw [hJoint π' «\sf{x}» «\sf{s}»]
      exact le_antisymm
        ((measure_mono Set.inter_subset_right).trans (le_of_eq hs0')) bot_le
    have hjs («\sf{x}» : α) : π (x ⁻¹' {«\sf{x}»} ∩ s ⁻¹' {«\sf{s}»}) = 0 := by
      rw [← hJoint π «\sf{x}» «\sf{s}»]
      exact h₀ «\sf{x}» «\sf{s}» (hjs' «\sf{x}»)
    have hun : s ⁻¹' {«\sf{s}»} = ⋃ «\sf{x}» : α, x ⁻¹' {«\sf{x}»} ∩ s ⁻¹' {«\sf{s}»} := by
      ext ω
      constructor
      · intro hω
        exact Set.mem_iUnion.mpr ⟨x ω, ⟨rfl, hω⟩⟩
      · intro hω
        obtain ⟨x0, hx0, hsω⟩ := Set.mem_iUnion.mp hω
        exact hsω
    have hdisj : Pairwise fun a b =>
        Disjoint (x ⁻¹' {a} ∩ s ⁻¹' {«\sf{s}»}) (x ⁻¹' {b} ∩ s ⁻¹' {«\sf{s}»}) :=
      fun a b hab => Set.disjoint_left.mpr fun ω h₃ h₄ => hab (h₃.1.symm.trans h₄.1)
    have hmeas («\sf{x}» : α) : MeasurableSet (x ⁻¹' {«\sf{x}»} ∩ s ⁻¹' {«\sf{s}»}) :=
      (hx (measurableSet_singleton «\sf{x}»)).inter (hs (measurableSet_singleton «\sf{s}»))
    have hs0 : π (s ⁻¹' {«\sf{s}»}) = 0 := by
      rw [hun, measure_iUnion hdisj hmeas]
      simp [hjs]
    exact hpos ((Measure.map_apply hs (measurableSet_singleton «\sf{s}»)).trans hs0)
  rw [Expectation.condEval_eq_condEvent hx hs hpos,
      Expectation.condEval_eq_condEvent hx hs hpos']
  have hto (φ : Measure Ω) [IsProbabilityMeasure φ] (g : α → E) :
    Expectation.condEvent φ x s g «\sf{s}» =
      ∫ ω, g (x ω) ∂φ[|s ⁻¹' {«\sf{s}»}] := by
    rw [Expectation.condEvent, expectation_bochner]
    apply integral_map (μ := φ[|s ⁻¹' {«\sf{s}»}]) hx.aemeasurable
      StronglyMeasurable.of_discrete.aestronglyMeasurable
  have hMass (φ : Measure Ω) [IsProbabilityMeasure φ] [SinglePSpace φ (x, s)] («\sf{x}» : α) :
    (φ[|s ⁻¹' {«\sf{s}»}].map x).real {«\sf{x}»} = ℙ[φ](x = «\sf{x}» | s = «\sf{s}») := by
    rw [measureReal_def, Measure.map_apply hx (measurableSet_singleton «\sf{x}»),
      cond_apply (hs (measurableSet_singleton «\sf{s}»)), Set.inter_comm,
      ← ENNReal.div_eq_inv_mul,
      _root_.Random.Prob_Cond.eq.Div.of.SinglePSpace inferInstance «\sf{x}» «\sf{s}»]
  have hSum (φ : Measure Ω) [IsProbabilityMeasure φ] (g : α → E) :
    ∫ ω, g (x ω) ∂φ[|s ⁻¹' {«\sf{s}»}] =
      ∑ «\sf{x}», (φ[|s ⁻¹' {«\sf{s}»}].map x).real {«\sf{x}»} • g «\sf{x}» := by
    rw [(integral_map (μ := φ[|s ⁻¹' {«\sf{s}»}]) hx.aemeasurable
        StronglyMeasurable.of_discrete.aestronglyMeasurable).symm]
    apply integral_fintype Integrable.of_finite
  rw [hto π f,
    hto π' (fun «\sf{x}» =>
      ((ℙ[π](x = «\sf{x}» | s = «\sf{s}») / ℙ[π'](x = «\sf{x}» | s = «\sf{s}»)) : ℝ) •
        f «\sf{x}»),
    hSum π f,
    hSum π' (fun «\sf{x}» =>
      ((ℙ[π](x = «\sf{x}» | s = «\sf{s}») / ℙ[π'](x = «\sf{x}» | s = «\sf{s}»)) : ℝ) •
        f «\sf{x}»)]
  refine Finset.sum_congr rfl fun «\sf{x}» _ => ?_
  if hq : (π'[|s ⁻¹' {«\sf{s}»}].map x).real {«\sf{x}»} = 0 then
    have hp : (π[|s ⁻¹' {«\sf{s}»}].map x).real {«\sf{x}»} = 0 := by
      have hj' : π' (x ⁻¹' {«\sf{x}»} ∩ s ⁻¹' {«\sf{s}»}) = 0 := by
        rw [hMass π' «\sf{x}»,
          _root_.Random.Prob_Cond.eq.Div.of.SinglePSpace
            (inferInstance : SinglePSpace π' (x, s)) «\sf{x}» «\sf{s}»] at hq
        if hb : π' (s ⁻¹' {«\sf{s}»}) = 0 then
          have hle : π' (x ⁻¹' {«\sf{x}»} ∩ s ⁻¹' {«\sf{s}»}) ≤ π' (s ⁻¹' {«\sf{s}»}) :=
            measure_mono Set.inter_subset_right
          rw [hb] at hle
          apply le_antisymm hle bot_le
        else
          apply (ENNReal.div_eq_zero_iff.mp <|
            ((ENNReal.toReal_eq_zero_iff _).1 hq).resolve_right
              (ENNReal.div_ne_top (measure_ne_top _ _) hb)).resolve_right
            (measure_ne_top _ _)
      rw [hMass π «\sf{x}»,
        _root_.Random.Prob_Cond.eq.Div.of.SinglePSpace (inferInstance : SinglePSpace π (x, s)) «\sf{x}» «\sf{s}»,
        ← hJoint π «\sf{x}» «\sf{s}», h₀ «\sf{x}» «\sf{s}» (by rw [hJoint π' «\sf{x}» «\sf{s}», hj'])]
      simp
    simp [hq, hp]
  else
    have hratio :
      ℙ[π](x = «\sf{x}» | s = «\sf{s}») / ℙ[π'](x = «\sf{x}» | s = «\sf{s}») =
          (π[|s ⁻¹' {«\sf{s}»}].map x).real {«\sf{x}»} /
            (π'[|s ⁻¹' {«\sf{s}»}].map x).real {«\sf{x}»} := by
      simp [hMass π «\sf{x}», hMass π' «\sf{x}»]
    rw [smul_smul, hratio]
    grind


-- created on 2023-04-03
-- updated on 2026-11-13
