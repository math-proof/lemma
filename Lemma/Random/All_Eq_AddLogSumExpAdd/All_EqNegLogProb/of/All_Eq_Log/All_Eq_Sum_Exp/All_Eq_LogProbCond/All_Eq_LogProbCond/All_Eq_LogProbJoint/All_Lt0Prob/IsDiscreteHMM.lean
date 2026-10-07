import Lemma.Measure.Measure.eq.Count.of.EqMeasureCount.EqMeasureCount
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Random.PSpace_Joint
import Lemma.Random.IsHiddenMarkovPr.of.CondIndep.CondIndep
import Lemma.Random.Prob.eq.Measure.of.Eq_Count
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Lemma.Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Random.Sum.eq.Prob
import sympy.concrete.reduced
import sympy.stats.discrete_hmm
import Lemma.Real.Sum.eq.Sum
import Lemma.Fin.IteSnoc.eq.Ite.of.Le
import Lemma.Fin.Snoc_Last.eq.Last
import Lemma.Fin.Sum.eq.SumSumSnoc
import Lemma.Random.All_Imp_Eq.of.IsHiddenMarkovFac
import Lemma.Random.IsHiddenMarkovFac.of.All_Eq.IsHiddenMarkovPr
open MeasureTheory Measure Random ENNReal.ToRealCoe
open IsDiscreteHMM


@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  [Fintype Y] [DecidableEq Y]
  [NeZero (n : ℕ)]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {«x.bvar» : ℕ → X}
  {s : ℕ → (ℕ → Y) → ℝ}
  {e z x' : ℕ → Y → ℝ}
  {G : Y → Y → ℝ}
-- given
  (h : IsDiscreteHMM π x y)
  (h₁ : ∀ «y.bvar» : ℕ → Y,
    0 < ℙ[π](x[:n] = «x.bvar»[:n] ∧ y[:n] = «y.bvar»[:n]))
  (h₂ : ∀ (t : ℕ) «y.bvar»,
    s t «y.bvar» = (ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) : ℝ).log)
  (h₃ : ∀ t («y.bvar» : ℕ → Y),
    e t («y.bvar» t) = (ℙ[π]((x t) = «x.bvar» t | (y t) = «y.bvar» t) : ℝ).log)
  (h₄ : ∀ i («y.bvar» : ℕ → Y),
    G («y.bvar» (i + 1)) («y.bvar» i) = (ℙ[π]((y (i + 1)) = «y.bvar» (i + 1) | (y i) = «y.bvar» i) : ℝ).log)
  (h₅ : ∀ t a, z t a = ∑ ys : Fin t → Y, (s t (fun i => if h : i < t then ys ⟨i, h⟩ else a)).exp)
  (h₆ : ∀ t a, x' t a = (z t a).log) :
-- imply
  have : SinglePSpace π (y[:n], x[:n]) := PSpace_Joint.comm (π := π) (x := x[:n]) (y := y[:n]) inferInstance
  (∀ t, t + 1 < n → x' (t + 1) = (G + x' t).exp.sum.log + e (t + 1)) ∧
    ∀ «y.bvar», -(ℙ[π](y[:n] = «y.bvar»[:n] | x[:n] = «x.bvar»[:n]) : ℝ).log = (x' (n - 1)).exp.sum.log - s (n - 1) «y.bvar» := by
-- proof
  have ⟨hx, hy, hX, hY, h_emit, h_markov⟩ := h
  intro hYX
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne n)).symm⟩
  simp only [Nat.add_sub_cancel]
  replace hYX : SinglePSpace π (y[:m + 1], x[:m + 1]) := hYX
  have : ∀ k : ℕ, SinglePSpace π (x[:k], y[:k]) := fun k => inferInstance
  have : ∀ i, SinglePSpace π (y i) := fun i =>
    Random.SinglePSpace.of.EqMeasureCount.Measurable (hy i) hY
  have : ∀ i j, SinglePSpace π (y i, y j) := fun i j =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (hy i) (hy j) hY hY
  have hpos := h₁
  have h₃' : ∀ t a, e t a = (ℙ[π]((x t) = «x.bvar» t | (y t) = a) : ℝ).log := fun t a => by
    simpa using h₃ t (fun _ => a)
  have h₄' : ∀ i a b, G a b = (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ).log := fun i a b => by
    simpa using h₄ i (fun k => if k = i + 1 then a else b)
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → (ℕ → Y) → ℝ, ∀ t «y.bvar», P t «y.bvar» = (ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) : ℝ) := ⟨fun t «y.bvar» => (ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) : ℝ), fun _ _ => rfl⟩
  have hpair : ∀ k : ℕ, ReferenceMeasure.measure (α := (Fin k → X) × (Fin k → Y)) = Measure.count := fun k =>
    Measure.Measure.eq.Count.of.EqMeasureCount.EqMeasureCount rfl rfl
  have hQ : ∀ (ys : ℕ → Y) (k : ℕ), (ℙ[π](x[:(k : ℤ)] = «x.bvar»[:(k : ℤ)] ∧ y[:(k : ℤ)] = ys[:(k : ℤ)]) : ENNReal) =
      π {ω | (∀ i < k, x i ω = «x.bvar» i) ∧ ∀ i < k, y i ω = ys i} := by
    intro ys k
    rw [Random.Prob.eq.Measure.of.Eq_Count (hpair k)]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, JointRandomSymbol, Prod.mk.injEq, funext_iff]
    constructor
    · intro h
      exact ⟨fun i hi => h.1 ⟨i, hi⟩, fun i hi => h.2 ⟨i, hi⟩⟩
    · intro h
      exact ⟨fun i => h.1 i i.2, fun i => h.2 i i.2⟩
  have hM : ∀ ys : ℕ → Y, π {ω | (∀ i < m + 1, x i ω = «x.bvar» i) ∧ ∀ i < m + 1, y i ω = ys i} ≠ 0 := fun ys h0 =>
    (hpos ys).ne' ((hQ ys (m + 1)).trans h0)
  have h₁ : ∀ t ≤ m, ∀ «y.bvar», 0 < P t «y.bvar» := by
    intro t ht ys
    rw [hPdef]
    refine ENNReal.toReal_pos (fun h0 => hM ys ?_) (fun h => measure_ne_top π _ ((hQ ys (t + 1)).symm.trans h))
    have h0' := (hQ ys (t + 1)).symm.trans h0
    have hsub : {ω | (∀ i < m + 1, x i ω = «x.bvar» i) ∧ ∀ i < m + 1, y i ω = ys i} ⊆ {ω | (∀ i < t + 1, x i ω = «x.bvar» i) ∧ ∀ i < t + 1, y i ω = ys i} :=
      fun ω h => ⟨fun i hi => h.1 i (by omega), fun i hi => h.2 i (by omega)⟩
    exact measure_mono_null hsub h0'
  have hE' : ∀ t ≤ m, ∀ a, 0 < (ℙ[π]((x t) = «x.bvar» t | (y t) = a) : ℝ) := by
    intro t ht a
    have hdiv := Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := π) (x := x t) (y := y t) hX hY («x.bvar» t) a
    show 0 < ((ℙ[π]((x t) = «x.bvar» t | (y t) = a) : ENNReal)).toReal
    rw [hdiv]
    have hsub : {ω | (∀ i < m + 1, x i ω = «x.bvar» i) ∧ ∀ i < m + 1, y i ω = (fun _ => a) i} ⊆ x t ⁻¹' {«x.bvar» t} ∩ y t ⁻¹' {a} :=
      fun ω h => ⟨h.1 t (by omega), h.2 t (by omega)⟩
    have hne : π (x t ⁻¹' {«x.bvar» t} ∩ y t ⁻¹' {a}) ≠ 0 := fun h0 => hM (fun _ => a) (measure_mono_null hsub h0)
    have hne' : π (y t ⁻¹' {a}) ≠ 0 := fun h0 => hne (measure_mono_null Set.inter_subset_right h0)
    exact ENNReal.toReal_pos (ENNReal.div_pos_iff.mpr ⟨hne, measure_ne_top _ _⟩).ne' (ENNReal.div_lt_top (measure_ne_top _ _) hne').ne
  have hT' : ∀ i, i + 1 ≤ m → ∀ a b, 0 < (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ) := by
    intro i hi a b
    have hdiv := Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := π) (x := y (i + 1)) (y := y i) hY hY a b
    show 0 < ((ℙ[π]((y (i + 1)) = a | (y i) = b) : ENNReal)).toReal
    rw [hdiv]
    have hsub : {ω | (∀ k < m + 1, x k ω = «x.bvar» k) ∧ ∀ k < m + 1, y k ω = (fun k => if k = i + 1 then a else b) k} ⊆ y (i + 1) ⁻¹' {a} ∩ y i ⁻¹' {b} :=
      fun ω h => ⟨by simpa using h.2 (i + 1) (by omega), by simpa using h.2 i (by omega)⟩
    have hne : π (y (i + 1) ⁻¹' {a} ∩ y i ⁻¹' {b}) ≠ 0 := fun h0 => hM (fun k => if k = i + 1 then a else b) (measure_mono_null hsub h0)
    have hne' : π (y i ⁻¹' {b}) ≠ 0 := fun h0 => hne (measure_mono_null Set.inter_subset_right h0)
    exact ENNReal.toReal_pos (ENNReal.div_pos_iff.mpr ⟨hne, measure_ne_top _ _⟩).ne' (ENNReal.div_lt_top (measure_ne_top _ _) hne').ne
  have h₀ : IsHiddenMarkovPr π x y «x.bvar» :=
    Random.IsHiddenMarkovPr.of.CondIndep.CondIndep h
  have h₀ := IsHiddenMarkovFac.of.All_Eq.IsHiddenMarkovPr h₀ hPdef
  have h₂ : ∀ t «y.bvar», s t «y.bvar» = (P t «y.bvar»).log := fun t «y.bvar» => by rw [h₂, hPdef]
  have hpre := All_Imp_Eq.of.IsHiddenMarkovFac h₀
  have hz : ∀ t ≤ m, ∀ a, z t a = ∑ ys0 : Fin t → Y, P t (fun i => if h : i < t then ys0 ⟨i, h⟩ else a) := by
    intro t ht a
    rw [h₅]
    refine Finset.sum_congr rfl fun ys0 _ => ?_
    rw [h₂, Real.exp_log (h₁ t ht _)]
  have hzpos : ∀ t ≤ m, ∀ a, 0 < z t a := by
    intro t ht a
    have : Nonempty Y := ⟨a⟩
    rw [hz t ht]
    exact Finset.sum_pos (fun _ _ => h₁ t ht _) Finset.univ_nonempty
  have hrec : ∀ t, t + 1 ≤ m → ∀ a, z (t + 1) a = (∑ b, z t b * (ℙ[π]((y (t + 1)) = a | (y t) = b) : ℝ)) * (ℙ[π]((x (t + 1)) = «x.bvar» (t + 1) | (y (t + 1)) = a) : ℝ) := by
    intro t ht a
    rw [hz (t + 1) ht, Fin.Sum.eq.SumSumSnoc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hz t (by omega), Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ys1 _ => ?_
    rw [(h₀ _).2 t, hpre t _ _ fun i hi => Fin.IteSnoc.eq.Ite.of.Le hi ys1 b a]
    rw [dif_neg (lt_irrefl (t + 1)), dif_pos (Nat.lt_succ_self t), Fin.Snoc_Last.eq.Last]
    ring
  refine ⟨fun t ht => ?_, fun «y.bvar» => ?_⟩
  ·
    have ht : t < m := by omega
    funext a
    have : Nonempty Y := ⟨a⟩
    show x' (t + 1) a = Real.log ((G + x' t).exp.sum a) + e (t + 1) a
    have hs : (G + x' t).exp.sum a = ∑ b, z t b * (ℙ[π]((y (t + 1)) = a | (y t) = b) : ℝ) :=
      Finset.sum_congr rfl fun b _ => by
        show Real.exp (G a b + x' t b) = _
        rw [add_comm (G a b), Real.exp_add, h₆, h₄' t a b, Real.exp_log (hzpos t ht.le b), Real.exp_log (hT' t ht a b)]
    rw [h₆, hrec t ht a, Real.log_mul (Finset.sum_pos (fun b _ => mul_pos (hzpos t ht.le b) (hT' t ht a b)) Finset.univ_nonempty).ne' (hE' (t + 1) ht a).ne', hs, h₃']
  ·
    have : Nonempty Y := ⟨«y.bvar» 0⟩
    have pad : ∀ (k : ℕ) (c : Y) (w : Fin k → Y), ((fun i : ℕ => if h : i < k then w ⟨i, h⟩ else c)[:k] : Fin k → Y) = w := by
      intro k c w
      funext i
      show (if h : i.val + 0 < k then w ⟨i.val + 0, h⟩ else c) = w i
      simp
    have e : ∀ ys' : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = «x.bvar»[:m + 1] ∧ y[:m + 1] = ys') : ℝ) = P m (fun i => if h : i < m + 1 then ys' ⟨i, h⟩ else «y.bvar» 0) := by
      intro ys'
      rw [hPdef]
      exact congrArg (fun w => (ℙ[π](x[:m + 1] = «x.bvar»[:m + 1] ∧ y[:m + 1] = w) : ℝ)) (pad (m + 1) («y.bvar» 0) ys').symm
    have hD : ∑ ys' : Fin (m + 1) → Y, P m (fun i => if h : i < m + 1 then ys' ⟨i, h⟩ else «y.bvar» 0) = (x' m).exp.sum := by
      rw [Real.Sum.eq.Sum, Fin.Sum.eq.SumSumSnoc]
      refine Finset.sum_congr rfl fun b _ => ?_
      show _ = Real.exp (x' m b)
      rw [h₆, Real.exp_log (hzpos m le_rfl b), hz m le_rfl]
      exact Finset.sum_congr rfl fun ys0 _ => hpre m _ _ fun i hi => Fin.IteSnoc.eq.Ite.of.Le hi ys0 b («y.bvar» 0)
    have hDpos : 0 < (x' m).exp.sum := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
    -- Bayes: Pr(y | x) = Pr(x ∧ y) / Pr(x), with Pr(x) = ∑ over the finite label space (total probability)
    have hrefXY : ReferenceMeasure.measure (α := (Fin (m + 1) → X) × (Fin (m + 1) → Y)) = Measure.count :=
      Measure.Measure.eq.Count.of.EqMeasureCount.EqMeasureCount rfl rfl
    have hrefYX : ReferenceMeasure.measure (α := (Fin (m + 1) → Y) × (Fin (m + 1) → X)) = Measure.count :=
      Measure.Measure.eq.Count.of.EqMeasureCount.EqMeasureCount rfl rfl
    have hmXY : ∀ a b, (ℙ[π](x[:m + 1] = a ∧ y[:m + 1] = b) : ENNReal) = π ((x[:m + 1], y[:m + 1]) ⁻¹' {(a, b)}) := by
      intro a b
      unfold Measure.prob
      rw [hrefXY, EqRnDeriv_Count, Measure.map_apply_of_aemeasurable (PSpace.aemeasurable (π := π)) (measurableSet_singleton _)]
    have hmYX : ∀ a b, (ℙ[π](y[:m + 1] = b ∧ x[:m + 1] = a) : ENNReal) = π ((x[:m + 1], y[:m + 1]) ⁻¹' {(a, b)}) := by
      intro a b
      unfold Measure.prob
      rw [hrefYX, EqRnDeriv_Count, Measure.map_apply_of_aemeasurable (PSpace.aemeasurable (π := π)) (measurableSet_singleton _)]
      congr 1
      ext ω
      simp [JointRandomSymbol, and_comm]
    have hden : ∑ b : Fin (m + 1) → Y, (ℙ[π](y[:m + 1] = b ∧ x[:m + 1] = «x.bvar»[:m + 1]) : ENNReal) = (π.map (fun ω => ((y[:m + 1], x[:m + 1]) ω).2)).rnDeriv ReferenceMeasure.measure («x.bvar»[:m + 1]) := by
      have := Sum.eq.Prob (π := π) (x := y[:m + 1]) (y := x[:m + 1]) hYX rfl rfl («x.bvar»[:m + 1])
      rwa [tsum_fintype] at this
    have h₇ : (ℙ[π](y[:m + 1] = «y.bvar»[:m + 1] | x[:m + 1] = «x.bvar»[:m + 1]) : ℝ) = (ℙ[π](x[:m + 1] = «x.bvar»[:m + 1] ∧ y[:m + 1] = «y.bvar»[:m + 1]) : ℝ) / ∑ ys' : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = «x.bvar»[:m + 1] ∧ y[:m + 1] = ys') : ℝ) := by
      have hfin : ∀ b : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = «x.bvar»[:m + 1] ∧ y[:m + 1] = b) : ENNReal) ≠ ⊤ := fun b => by
        rw [hmXY]; exact measure_ne_top _ _
      have hc : (ℙ[π](y[:m + 1] = «y.bvar»[:m + 1] | x[:m + 1] = «x.bvar»[:m + 1]) : ENNReal) = (ℙ[π](x[:m + 1] = «x.bvar»[:m + 1] ∧ y[:m + 1] = «y.bvar»[:m + 1]) : ENNReal) / ∑ b : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = «x.bvar»[:m + 1] ∧ y[:m + 1] = b) : ENNReal) := by
        unfold Measure.condProb
        rw [← hden, hmYX, ← hmXY]
        congr 1
        exact Finset.sum_congr rfl fun b _ => by rw [hmYX, hmXY]
      show ((ℙ[π](y[:m + 1] = «y.bvar»[:m + 1] | x[:m + 1] = «x.bvar»[:m + 1]) : ENNReal)).toReal = _
      rw [hc, ENNReal.toReal_div, ENNReal.toReal_sum fun b _ => hfin b]
    show -(ℙ[π](y[:m + 1] = «y.bvar»[:m + 1] | x[:m + 1] = «x.bvar»[:m + 1]) : ℝ).log = (x' m).exp.sum.log - s m «y.bvar»
    rw [h₇, Finset.sum_congr rfl (fun ys' _ => e ys'), hD, ← hPdef m «y.bvar», Real.log_div (h₁ m le_rfl _).ne' hDpos.ne', ← h₂]
    ring


-- created on 2018-12-21
-- updated on 2026-10-04
