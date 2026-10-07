import Lemma.Measure.Measure.eq.Count.of.EqMeasureCount.EqMeasureCount
import Lemma.Random.IsHiddenMarkovPr.of.CondIndep.CondIndep
import Lemma.Random.Prob.eq.Measure.of.Eq_Count
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import sympy.stats.discrete_hmm
import sympy.stats.hidden_markov_sequence
import sympy.concrete.max
import sympy.concrete.reduced
import sympy.core.numbers
import sympy.Basic
import Lemma.Finset.Max.eq.SupUniv
import Lemma.Fin.IteSnoc.eq.Ite.of.Le
import Lemma.Fin.Snoc_Last.eq.Last
import Lemma.Finset.SupUniv.eq.SupUnivSupUnivSnoc
import Lemma.Finset.SupAdd.eq.AddSup
import Lemma.Random.All_Imp_Eq.of.IsHiddenMarkovFac
import Lemma.Random.IsHiddenMarkovFac.of.All_Eq.IsHiddenMarkovPr
open Finset MeasureTheory Measure Random
open IsDiscreteHMM
open scoped ENNReal.ToRealCoe


@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [NeZero (n : ℕ)]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {«x.bvar» : ℕ → X}
  {s : ℕ → (ℕ → Y) → ℝ}
  {e x' : ℕ → Y → ℝ}
  {G : Y → Y → ℝ}
-- given
  (h₀ : IsDiscreteHMM π x y)
  (h₁ : ∀ t («y.bvar» : ℕ → Y), 0 < (ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) : ℝ))
  (h₂ : ∀ t «y.bvar», s t «y.bvar» = (ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) : ℝ).log)
  (h₃ : ∀ t («y.bvar» : ℕ → Y), e t («y.bvar» t) = (ℙ[π]((x t) = «x.bvar» t | (y t) = «y.bvar» t) : ℝ).log)
  (h₄ : ∀ i («y.bvar» : ℕ → Y),
    G («y.bvar» (i + 1)) («y.bvar» i) = (ℙ[π]((y (i + 1)) = «y.bvar» (i + 1) | (y i) = «y.bvar» i) : ℝ).log)
  (h₅ : ∀ t a, x' t a = max[«y.bvar» : Fin t → Y] s t (fun i => if h : i < t then «y.bvar» ⟨i, h⟩ else a)) :
-- imply
  (∀ t, x' (t + 1) = e (t + 1) + (G + x' t).max) ∧
    max[«y.bvar» : Fin n → Y] (ℙ[π](x[:n] = «x.bvar»[:n] ∧ y[:n] = «y.bvar») : ℝ) =
      (x' (n - 1)).max.exp := by
-- proof
  have ⟨_, _, hX, hY, _, _⟩ := h₀
  have : ∀ i, SinglePSpace π (y i) := fun i => IsDiscreteHMM.singlePSpace_y (x := x) i
  have : ∀ i j, SinglePSpace π (y i, y j) := fun i j => IsDiscreteHMM.singlePSpace_yy (x := x) i j
  have : ∀ k : ℕ, SinglePSpace π (x[:k], y[:k]) := fun k => inferInstance
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
  have hM : ∀ (t : ℕ) (ys : ℕ → Y), π {ω | (∀ i < t + 1, x i ω = «x.bvar» i) ∧ ∀ i < t + 1, y i ω = ys i} ≠ 0 := fun t ys h0 =>
    (h₁ t ys).ne' (by
      show ((ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ENNReal)).toReal = 0
      have h' := hQ ys (t + 1)
      push_cast at h'
      rw [h'.trans h0]; rfl)
  have hE : ∀ t a, 0 < (ℙ[π]((x t) = «x.bvar» t | (y t) = a) : ℝ) := by
    intro t a
    have hdiv := Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := π) (x := x t) (y := y t) hX hY («x.bvar» t) a
    show 0 < ((ℙ[π]((x t) = «x.bvar» t | (y t) = a) : ENNReal)).toReal
    rw [hdiv]
    have hsub : {ω | (∀ i < t + 1, x i ω = «x.bvar» i) ∧ ∀ i < t + 1, y i ω = (fun _ => a) i} ⊆ x t ⁻¹' {«x.bvar» t} ∩ y t ⁻¹' {a} :=
      fun ω h => ⟨h.1 t (by omega), h.2 t (by omega)⟩
    have hne : π (x t ⁻¹' {«x.bvar» t} ∩ y t ⁻¹' {a}) ≠ 0 := fun h0 => hM t (fun _ => a) (measure_mono_null hsub h0)
    have hne' : π (y t ⁻¹' {a}) ≠ 0 := fun h0 => hne (measure_mono_null Set.inter_subset_right h0)
    exact ENNReal.toReal_pos (ENNReal.div_pos_iff.mpr ⟨hne, measure_ne_top _ _⟩).ne' (ENNReal.div_lt_top (measure_ne_top _ _) hne').ne
  have hT : ∀ i a b, 0 < (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ) := by
    intro i a b
    have hdiv := Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := π) (x := y (i + 1)) (y := y i) hY hY a b
    show 0 < ((ℙ[π]((y (i + 1)) = a | (y i) = b) : ENNReal)).toReal
    rw [hdiv]
    have hsub : {ω | (∀ k < i + 1 + 1, x k ω = «x.bvar» k) ∧ ∀ k < i + 1 + 1, y k ω = (fun k => if k = i + 1 then a else b) k} ⊆ y (i + 1) ⁻¹' {a} ∩ y i ⁻¹' {b} :=
      fun ω h => ⟨by simpa using h.2 (i + 1) (by omega), by simpa using h.2 i (by omega)⟩
    have hne : π (y (i + 1) ⁻¹' {a} ∩ y i ⁻¹' {b}) ≠ 0 := fun h0 => hM (i + 1) (fun k => if k = i + 1 then a else b) (measure_mono_null hsub h0)
    have hne' : π (y i ⁻¹' {b}) ≠ 0 := fun h0 => hne (measure_mono_null Set.inter_subset_right h0)
    exact ENNReal.toReal_pos (ENNReal.div_pos_iff.mpr ⟨hne, measure_ne_top _ _⟩).ne' (ENNReal.div_lt_top (measure_ne_top _ _) hne').ne
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → (ℕ → Y) → ℝ, ∀ t «y.bvar», P t «y.bvar» = (ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) : ℝ) := ⟨fun t «y.bvar» => (ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) : ℝ), fun _ _ => rfl⟩
  have h₁ : ∀ t «y.bvar», 0 < P t «y.bvar» := fun t «y.bvar» => by rw [hPdef]; exact h₁ t «y.bvar»
  have h₀ : IsHiddenMarkovFac π x y «x.bvar» P := IsHiddenMarkovFac.of.All_Eq.IsHiddenMarkovPr (IsHiddenMarkovPr.of.CondIndep.CondIndep h₀) hPdef
  have h₂ : ∀ t «y.bvar», s t «y.bvar» = (P t «y.bvar»).log := fun t «y.bvar» => by rw [h₂, hPdef]
  have hpre := All_Imp_Eq.of.IsHiddenMarkovFac h₀
  have h₃ : ∀ t a, e t a = (ℙ[π]((x t) = «x.bvar» t | (y t) = a) : ℝ).log := fun t a => h₃ t (fun _ => a)
  have hTt := hT
  have h₄ : ∀ i a b, G a b = (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ).log := fun i a b => by
    simpa using h₄ i (fun j => if j = i then b else a)
  have hGt := h₄
  have hstep : ∀ t a b (ys0 : Fin t → Y),
      s (t + 1) (fun i => if h : i < t + 1 then Fin.snoc (α := fun _ => Y) ys0 b ⟨i, h⟩ else a) =
        s t (fun i => if h : i < t then ys0 ⟨i, h⟩ else b) + G a b + e (t + 1) a := by
    intro t a b ys0
    rw [h₂, h₂, (h₀ _).2 t, hpre t _ _ fun i hi => Fin.IteSnoc.eq.Ite.of.Le hi ys0 b a]
    rw [dif_neg (lt_irrefl (t + 1)), dif_pos (Nat.lt_succ_self t), Fin.Snoc_Last.eq.Last,
      Real.log_mul (h₁ _ _).ne' (mul_pos (hTt t a b) (hE _ a)).ne', Real.log_mul (hTt t a b).ne' (hE _ a).ne', hGt t a b, h₃]
    ring
  refine ⟨fun t => ?_, ?_⟩
  ·
    funext a
    show x' (t + 1) a = e (t + 1) a + Finset.univ.sup' Finset.univ_nonempty (fun b => G a b + x' t b)
    rw [h₅, SupUniv.eq.SupUnivSupUnivSnoc]
    simp only [hstep, SupAdd.eq.AddSup]
    rw [add_comm]
    congr 1
    refine Finset.sup'_congr _ rfl fun b _ => ?_
    show _ = G a b + x' t b
    rw [h₅, add_comm]
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne n)).symm⟩
    simp only [Nat.add_sub_cancel]
    have pad : ∀ (k : ℕ) (c : Y) (w : Fin k → Y), ((fun i : ℕ => if h : i < k then w ⟨i, h⟩ else c)[:k] : Fin k → Y) = w := by
      intro k c w
      funext i
      show (if h : i.val + 0 < k then w ⟨i.val + 0, h⟩ else c) = w i
      simp
    have e : ∀ «y.bvar» : Fin (m + 1) → Y, (ℙ[π](x[:(m + 1 : ℕ)] = «x.bvar»[:(m + 1 : ℕ)] ∧ y[:(m + 1 : ℕ)] = «y.bvar») : ℝ) = P (m + 1 - 1) (fun i => if h : i < m + 1 then «y.bvar» ⟨i, h⟩ else Classical.arbitrary Y) := by
      intro «y.bvar»
      rw [Nat.add_sub_cancel, hPdef]
      exact congrArg (fun w => (ℙ[π](x[:(m + 1 : ℕ)] = «x.bvar»[:(m + 1 : ℕ)] ∧ y[:(m + 1 : ℕ)] = w) : ℝ)) (pad (m + 1) (Classical.arbitrary Y) «y.bvar»).symm
    simp only [e]
    rw [Nat.add_sub_cancel, SupUniv.eq.SupUnivSupUnivSnoc, Max.eq.SupUniv,
      Finset.apply_sup'_eq_sup'_comp _ Real.exp (fun u v => Real.exp_monotone.map_sup u v)]
    refine Finset.sup'_congr _ rfl fun b _ => ?_
    rw [Function.comp_apply]
    show _ = Real.exp (x' m b)
    rw [h₅, Finset.apply_sup'_eq_sup'_comp _ Real.exp (fun u v => Real.exp_monotone.map_sup u v)]
    refine Finset.sup'_congr _ rfl fun ys0 _ => ?_
    rw [Function.comp_apply, h₂, Real.exp_log (h₁ _ _)]
    exact hpre m _ _ fun i hi => Fin.IteSnoc.eq.Ite.of.Le hi ys0 b _


-- created on 2020-12-20
-- updated on 2025-04-20
