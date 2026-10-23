import Lemma.Random.ProbCond.eq.Div.of.SinglePSpace
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Probability.Independence.Conditional
import sympy.stats.hidden_markov_sequence
import sympy.stats.single_pspace_measurable
open MeasureTheory ProbabilityTheory Measure Random Fun
open scoped ProbabilityTheory


/--
Bayes product for a label `x` and document features `y`. If each feature `y[t]`
is conditionally independent of its prefix given the label,
`y[t] ⟂ᵢ[π] y[:t] | x`, and the joint atom is nonzero, then
`ℙ(x = «x.bvar» | y[:m] = «y.bvar»[:m]) =
  ℙ(x = «x.bvar») * (∏ j, ℙ(y[j] = «y.bvar»[j] | x = «x.bvar»)) / ℙ(y[:m] = «y.bvar»[:m])`.

In NLP this is the core identity behind naive Bayes document classification
(text categorization): bag-of-words features `y`, keywords/labels `x`.

`[Fact (Measurable x)]` and `[Fact (Measurable y[:m])]` feed
`SinglePSpace π (x, y[:m])`, so the joint binder is not an argument.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure α] [CountableMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} [Fact (Measurable x)]
  {y : ℕ ⇀ Ω → β} {m : ℕ} [Fact (Measurable y[:m])]
  {«x.bvar» : α} {«y.bvar» : ℕ ⇀ β}
-- given
  (h₀ : ∀ t : ℕ, 0 < t → t < m → y[t] ⟂ᵢ[x, ‹Fact (Measurable x)›.out; π] y[:t])
  (h₁ : ℙ[π](x = «x.bvar» ∧ y[:m] = «y.bvar»[:m]) ≠ 0) :
-- imply
  have : SinglePSpace π x :=
    PSpace.of.PSpace_Joint.fst
      (inferInstance : SinglePSpace π (x, show Ω → Fin m → β from y[:m]))
  have : SinglePSpace π y[:m] :=
    SinglePSpace.of.EqMeasureCount.Measurable ‹Fact (Measurable y[:m])›.out rfl
  have : ∀ j : Fin m, SinglePSpace π (y[j], x) :=
    fun j => SinglePSpace.of.Measurable.Measurable ((measurable_pi_apply j).comp ‹Fact (Measurable y[:m])›.out) ‹Fact (Measurable x)›.out
  ℙ[π](x = «x.bvar» | y[:m] = «y.bvar»[:m]) =
    ℙ[π](x = «x.bvar») *
      (∏ j : Fin m, ℙ[π](y[j] = «y.bvar»[j] | x = «x.bvar»)) /
      ℙ[π](y[:m] = «y.bvar»[:m]) := by
-- proof
  intro hxs hys hyx
  let a : α := «x.bvar»
  let b : ℕ → β := ⇑«y.bvar»
  let ys : Ω → Fin m → β := y[:m]
  let A : Set Ω := x ⁻¹' {a}
  let prefixSet : ℕ → Set Ω := fun k => ⋂ j : Fin k, y[j] ⁻¹' {b j}
  have hA : MeasurableSet A := ‹Fact (Measurable x)›.out (measurableSet_singleton a)
  have hAtop : π A ≠ ⊤ := measure_ne_top π A
  have hyj : ∀ j : Fin m, Measurable y[j] :=
    fun j => (measurable_pi_apply j).comp ‹Fact (Measurable y[:m])›.out
  have hslice_meas (k : ℕ) (hk : k ≤ m) : Measurable (show Ω → Fin k → β from y[:k]) := by
    apply Measurable.of_eval
    intro i
    have : (fun ω => y[:k] ω i) = fun ω => y[:m] ω ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
      funext ω
      rfl
    rw [this]
    exact (measurable_pi_apply _).comp ‹Fact (Measurable y[:m])›.out
  have hslice_apply {k : ℕ} {ω : Ω} {j : Fin k} :
    y[:k] ω j = (y (j + 0)) ω := by
    rfl
  have hb_apply {k : ℕ} {j : Fin k} : b[:k] j = b (j + 0) := by
    unfold Function.getSlice
    dsimp only [FunSlice.slice]
    rfl
  have hslice_set (k : ℕ) :
    (show Ω → Fin k → β from y[:k]) ⁻¹' {b[:k]} = prefixSet k := by
    ext ω
    simp only [prefixSet, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    ·
      intro h j
      have hij := congrFun h j
      rw [hslice_apply, hb_apply] at hij
      simpa using hij
    ·
      intro h
      funext j
      rw [hslice_apply, hb_apply]
      simpa using h j
  have hinter (k : ℕ) : prefixSet (k + 1) = prefixSet k ∩ (y k) ⁻¹' {b k} := by
    ext ω
    simp only [prefixSet, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    ·
      intro h
      exact ⟨fun j => h j.castSucc, h (Fin.last k)⟩
    ·
      intro h j
      refine Fin.lastCases ?_ (fun i => ?_) j
      ·
        exact h.2
      ·
        exact h.1 i
  have hrefm : ReferenceMeasure.measure (α := Fin m → β) = Measure.count := rfl
  have hrefprod : ReferenceMeasure.measure (α := α × (Fin m → β)) = Measure.count := by
    change (ReferenceMeasure.measure (α := α)).prod
      (ReferenceMeasure.measure (α := Fin m → β)) = Measure.count
    rw [CountableMeasure.measure_eq_count, hrefm, ProdCountS.eq.Count]
  have hjoint : π (A ∩ ys ⁻¹' {b[:m]}) ≠ 0 := by
    let z : Ω → α × (Fin m → β) := (x, show Ω → Fin m → β from y[:m])
    have hz : z = fun ω => (x ω, y[:m] ω) := rfl
    have hprob :
      π.prob z («x.bvar», show Fin m → β from «y.bvar»[:m]) =
        π (z ⁻¹' {(«x.bvar», show Fin m → β from «y.bvar»[:m])}) :=
      Prob.eq.Measure.of.Eq_Count hrefprod _
    have hpre : z ⁻¹' {(a, show Fin m → β from b[:m])} = A ∩ ys ⁻¹' {b[:m]} := by
      rw [hz]
      ext ω
      simp [A, ys, Prod.ext_iff]
    rw [hpre] at hprob
    simpa [a, b, ys] using hprob.symm.trans_ne h₁
  have hA0 : π A ≠ 0 := by
    intro h0
    apply hjoint
    exact measure_mono_null Set.inter_subset_left h0
  have hratio : ∀ k, k ≤ m →
    π (A ∩ prefixSet k) / π A =
      ∏ j : Fin k, π (A ∩ y[j] ⁻¹' {b j}) / π A := by
    intro k hk
    induction k with
    | zero =>
      have h0 : prefixSet 0 = Set.univ := by
        ext ω
        simp [prefixSet]
      simp [h0, Set.inter_univ, ENNReal.div_self hA0 hAtop]
    | succ k ih =>
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have ih := ih hk'
      have hL : π (A ∩ prefixSet (k + 1)) * π A =
        π (A ∩ (y k) ⁻¹' {b k}) * π (A ∩ prefixSet k) := by
        if hk0 : k = 0 then
          subst hk0
          have hU : prefixSet 0 = Set.univ := by
            ext ω
            simp [prefixSet]
          rw [hinter 0, hU, Set.univ_inter, Set.inter_univ]
        else
          have ht0 : 0 < k := Nat.pos_of_ne_zero hk0
          have htm : k < m := Nat.lt_of_succ_le hk
          have hm' := ‹Fact (Measurable x)›.out.comap_le
          let S : Set Ω := (y k) ⁻¹' {b k}
          let T : Set Ω := (show Ω → Fin k → β from y[:k]) ⁻¹' {b[:k]}
          have hyk : Measurable (y k) := hyj ⟨k, htm⟩
          have hS : MeasurableSet S := hyk (measurableSet_singleton _)
          have hT : MeasurableSet T := (hslice_meas k (Nat.le_of_lt htm)) (measurableSet_singleton _)
          have hST : MeasurableSet (S ∩ T) := hS.inter hT
          have hAm : MeasurableSet[MeasurableSpace.comap x inferInstance] A :=
            ⟨{a}, measurableSet_singleton a, rfl⟩
          have hci :=
            ((condIndepFun_iff_condExp_inter_preimage_eq_mul hyk (hslice_meas k (Nat.le_of_lt htm))).1
              (h₀ k ht0 htm)) {b k} {show Fin k → β from b[:k]}
              (measurableSet_singleton _) (measurableSet_singleton _)
          have hint (U : Set Ω) (hU : MeasurableSet U) :
            Integrable (U.indicator fun _ : Ω => (1 : ℝ)) π :=
            (integrable_const _).indicator hU
          have hmass (U : Set Ω) (hU : MeasurableSet U) :
            ∫ ω in A, (π⟦U | MeasurableSpace.comap x inferInstance⟧) ω ∂π =
              (π (A ∩ U)).toReal := by
            rw [setIntegral_condExp hm' (hint U hU) hAm, ← integral_indicator hA,
              Set.indicator_indicator, integral_indicator (hA.inter hU), setIntegral_const,
              Measure.real_def, smul_eq_mul, mul_one]
          have hAne : A.Nonempty := by
            apply Set.nonempty_iff_ne_empty.2
            intro hempty
            apply hA0
            simp [hempty]
          let ω0 : Ω := hAne.some
          have hω0 : ω0 ∈ A := hAne.some_mem
          have hconst (U : Set Ω) (hU : MeasurableSet U) :
            ∀ ω ∈ A, (π⟦U | MeasurableSpace.comap x inferInstance⟧) ω =
              (π⟦U | MeasurableSpace.comap x inferInstance⟧) ω0 := by
            intro ω hω
            apply stronglyMeasurable_condExp.factorsThrough
            have hxω : x ω = a := by simpa [A] using hω
            have hx0 : x ω0 = a := by simpa [A] using hω0
            rw [hxω, hx0]
          have hscale (U : Set Ω) (hU : MeasurableSet U) :
            (π⟦U | MeasurableSpace.comap x inferInstance⟧) ω0 * (π A).toReal =
              (π (A ∩ U)).toReal := by
            have hfun : ∫ ω in A, (π⟦U | MeasurableSpace.comap x inferInstance⟧) ω ∂π =
              (π⟦U | MeasurableSpace.comap x inferInstance⟧) ω0 * (π A).toReal := by
              rw [setIntegral_congr_fun hA (fun ω hω => hconst U hU ω hω),
                setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
            rw [← hfun, hmass U hU]
          have hprod_int : ∫ ω in A, (π⟦S ∩ T | MeasurableSpace.comap x inferInstance⟧) ω ∂π =
            (π (A ∩ S)).toReal * (π (A ∩ T)).toReal / (π A).toReal := by
            have hcongr : ∫ ω in A, (π⟦S ∩ T | MeasurableSpace.comap x inferInstance⟧) ω ∂π =
              ∫ ω in A, (π⟦S | MeasurableSpace.comap x inferInstance⟧) ω *
                (π⟦T | MeasurableSpace.comap x inferInstance⟧) ω ∂π :=
              setIntegral_congr_ae (hm' A hAm) (hci.mono fun ω hω _ => hω)
            rw [hcongr]
            have hpt : ∀ ω ∈ A,
              (π⟦S | MeasurableSpace.comap x inferInstance⟧) ω *
                (π⟦T | MeasurableSpace.comap x inferInstance⟧) ω =
                (π⟦S | MeasurableSpace.comap x inferInstance⟧) ω0 *
                  (π⟦T | MeasurableSpace.comap x inferInstance⟧) ω0 := by
              intro ω hω
              rw [hconst S hS ω hω, hconst T hT ω hω]
            rw [setIntegral_congr_fun hA hpt, setIntegral_const, Measure.real_def,
              smul_eq_mul]
            have hs := hscale S hS
            have ht := hscale T hT
            have hp : (π A).toReal ≠ 0 := (ENNReal.toReal_pos hA0 hAtop).ne'
            rw [eq_div_iff hp]
            calc
              _ = ((π⟦S | MeasurableSpace.comap x inferInstance⟧) ω0 * (π A).toReal) *
                  ((π⟦T | MeasurableSpace.comap x inferInstance⟧) ω0 * (π A).toReal) := by
                ring
              _ = (π (A ∩ S)).toReal * (π (A ∩ T)).toReal := by
                rw [hs, ht]
          have hmassST : ∫ ω in A, (π⟦S ∩ T | MeasurableSpace.comap x inferInstance⟧) ω ∂π =
            (π (A ∩ (S ∩ T))).toReal := by
            simpa [Set.inter_assoc, Set.inter_comm A (S ∩ T), Set.inter_left_comm A S T] using
              hmass (S ∩ T) hST
          have hneL : π (A ∩ (S ∩ T)) ≠ ⊤ := measure_ne_top _ _
          have hneR : π (A ∩ S) * π (A ∩ T) / π A ≠ ⊤ :=
            ENNReal.div_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) hA0
          have hreal : (π (A ∩ (S ∩ T))).toReal =
            (π (A ∩ S) * π (A ∩ T) / π A).toReal := by
            rw [ENNReal.toReal_div, ENNReal.toReal_mul, ← hmassST, hprod_int]
          have heq : π (A ∩ (S ∩ T)) = π (A ∩ S) * π (A ∩ T) / π A :=
            (ENNReal.toReal_eq_toReal_iff' hneL hneR).mp hreal
          have hsets : A ∩ prefixSet (k + 1) = A ∩ (S ∩ T) := by
            dsimp only [S, T]
            rw [hinter k, hslice_set k]
            ac_rfl
          have hSset : A ∩ S = A ∩ (y k) ⁻¹' {b k} := by
            dsimp only [S]
          have hTset : A ∩ T = A ∩ prefixSet k := by
            dsimp only [T]
            rw [hslice_set k]
          rw [hsets, heq, mul_comm, ENNReal.mul_div_cancel hA0 hAtop, hSset, hTset]
      have hdiv : π (A ∩ prefixSet (k + 1)) / π A =
        (π (A ∩ (y k) ⁻¹' {b k}) / π A) * (π (A ∩ prefixSet k) / π A) := by
        apply (ENNReal.toReal_eq_toReal_iff'
          (ENNReal.div_ne_top (measure_ne_top _ _) hA0)
          (ENNReal.mul_ne_top
            (ENNReal.div_ne_top (measure_ne_top _ _) hA0)
            (ENNReal.div_ne_top (measure_ne_top _ _) hA0))).mp
        rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div]
        have hreal : (π (A ∩ prefixSet (k + 1))).toReal * (π A).toReal =
          (π (A ∩ (y k) ⁻¹' {b k})).toReal * (π (A ∩ prefixSet k)).toReal := by
          rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, hL]
        field_simp [(ENNReal.toReal_pos hA0 hAtop).ne']
        linear_combination hreal
      rw [Fin.prod_univ_castSucc, hdiv, ih, mul_comm]
      simp [Fin.val_last]
  have hC : ys ⁻¹' {b[:m]} = prefixSet m := hslice_set m
  have hmarg : ℙ[π](x = a) = π A := by
    simpa [a, A] using Prob.eq.Measure.of.Eq_Count (x := x) CountableMeasure.measure_eq_count a
  have hmargY : ℙ[π](ys = b[:m]) = π (ys ⁻¹' {b[:m]}) :=
    Prob.eq.Measure.of.Eq_Count (x := ys) hrefm b[:m]
  have hcond : ℙ[π](x = a | ys = b[:m]) =
    π (A ∩ ys ⁻¹' {b[:m]}) / π (ys ⁻¹' {b[:m]}) := by
    have h :
      ℙ[π](x = a | y[:m] = (show Fin m → β from b[:m])) =
        π (x ⁻¹' {a} ∩ (show Ω → Fin m → β from y[:m]) ⁻¹' {show Fin m → β from b[:m]}) /
          π ((show Ω → Fin m → β from y[:m]) ⁻¹' {show Fin m → β from b[:m]}) :=
      ProbCond.eq.Div.of.SinglePSpace inferInstance a (show Fin m → β from b[:m])
    simpa [a, A, ys, Set.inter_comm] using h
  have hfac : ∀ j : Fin m, ℙ[π](y[j] = b j | x = a) =
    π (A ∩ y[j] ⁻¹' {b j}) / π A := by
    intro j
    have h :
      ℙ[π](y[j] = b j | x = a) =
        π (y[j] ⁻¹' {b j} ∩ x ⁻¹' {a}) / π (x ⁻¹' {a}) :=
      ProbCond.eq.Div.of.SinglePSpace inferInstance (b j) a
    simpa [a, A, Set.inter_comm] using h
  have hprod : ∏ j : Fin m, ℙ[π](y[j] = b j | x = a) =
    π (A ∩ prefixSet m) / π A := by
    rw [Finset.prod_congr rfl (fun j _ => hfac j)]
    exact (hratio m le_rfl).symm
  calc
    _ = ℙ[π](x = a | ys = b[:m]) := rfl
    _ = π (A ∩ ys ⁻¹' {b[:m]}) / π (ys ⁻¹' {b[:m]}) := hcond
    _ = π A * (π (A ∩ ys ⁻¹' {b[:m]}) / π A) / π (ys ⁻¹' {b[:m]}) := by
      rw [ENNReal.mul_div_cancel hA0 hAtop]
    _ = ℙ[π](x = a) * (∏ j : Fin m, ℙ[π](y[j] = b j | x = a)) /
        ℙ[π](ys = b[:m]) := by
      rw [hC, ← hprod]
      rw [← hmarg, ← hC, ← hmargY]
    _ = ℙ[π](x = «x.bvar») *
        (∏ j : Fin m, ℙ[π](y[j] = «y.bvar»[j] | x = «x.bvar»)) /
        ℙ[π](y[:m] = «y.bvar»[:m]) := rfl


-- created on 2024-06-18
-- updated on 2026-10-22
