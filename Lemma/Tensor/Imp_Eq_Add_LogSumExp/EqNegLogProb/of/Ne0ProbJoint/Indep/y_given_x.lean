import Lemma.Measure.EqRnDeriv_Count
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.PSpace_Joint
import Lemma.Random.Sum.eq.Prob
import sympy.concrete.reduced
import sympy.stats.hidden_markov_sequence
import sympy.stats.ennreal_coe
import sympy.Basic
open MeasureTheory Measure Random
open scoped ENNReal.ToRealCoe


@[main]
private lemma main
  {Ω Y X : Type*} [MeasurableSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  [Fintype Y] [DecidableEq Y]
  {m : ℕ}
  {π : Measure Ω}
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {xo : ℕ → X}
  [∀ i, SinglePSpace π (y i)]
  [∀ i j, SinglePSpace π (x i, y j)]
  [∀ i j, SinglePSpace π (y i, y j)]
  [∀ n, SinglePSpace π (x[:n], y[:n])]
  {s : ℕ → (ℕ → Y) → ℝ}
  {e : ℕ → Y → ℝ}
  {G : Y → Y → ℝ}
  {z x' : ℕ → Y → ℝ}
-- given
  (h₀ : IsHiddenMarkovPr π x y xo)
  (h₁ : ∀ t (ys : ℕ → Y), 0 < (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ))
  (h₂ : ∀ t ys, s t ys = (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ).log)
  (h₃ : ∀ t a, e t a = (ℙ[π]((x t) = xo t | (y t) = a) : ℝ).log)
  (h₄ : ∀ i a b, G a b = (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ).log)
  (h₅ : ∀ t a, z t a = ∑ ys ∈ Finset.univ.filter (fun ys : Fin (t + 1) → Y => ys (Fin.last t) = a), (s t (fun i => if h : i < t + 1 then ys ⟨i, h⟩ else a)).exp)
  (h₆ : ∀ t a, x' t a = (z t a).log)
  (hT : ∀ i a b, 0 < (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ))
  (hE : ∀ t a, 0 < (ℙ[π]((x t) = xo t | (y t) = a) : ℝ)) :
-- imply
  have : SinglePSpace π (y[:m + 1], x[:m + 1]) :=
    PSpace_Joint.comm (π := π) (x := x[:m + 1]) (y := y[:m + 1]) (by infer_instance)
  (∀ t a, x' (t + 1) a = (x' t + G a).exp.sum.log + e (t + 1) a) ∧
    ∀ ys : ℕ → Y, -(ℙ[π](y[:m + 1] = ys[:m + 1] | x[:m + 1] = xo[:m + 1]) : ℝ).log = (x' m).exp.sum.log - s m ys := by
-- proof
  intro hYX
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → (ℕ → Y) → ℝ, ∀ t ys, P t ys = (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ) := ⟨fun t ys => (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ), fun _ _ => rfl⟩
  have h₁ : ∀ t ys, 0 < P t ys := fun t ys => by rw [hPdef]; exact h₁ t ys
  have h₀ := h₀.toFac hPdef
  have h₂ : ∀ t ys, s t ys = (P t ys).log := fun t ys => by rw [h₂, hPdef]
  have hpre := h₀.prefix
  have hTt := hT
  have hGt := h₄
  have hz : ∀ t a, z t a = ∑ ys0 : Fin t → Y, P t (fun i => if h : i < t then ys0 ⟨i, h⟩ else a) := by
    intro t a
    rw [h₅, Finset.sum_filter, Fintype.sum_snoc]
    simp only [Fin.snoc_last]
    rw [Finset.sum_eq_single a (fun b _ hb => Finset.sum_eq_zero fun ys0 _ => if_neg hb) (by simp)]
    refine Finset.sum_congr rfl fun ys0 _ => ?_
    rw [if_pos rfl, h₂, Real.exp_log (h₁ _ _)]
    exact hpre t _ _ fun i hi => dite_snoc_eq ys0 a a hi
  have hzpos : ∀ t a, 0 < z t a := by
    intro t a
    have : Nonempty Y := ⟨a⟩
    rw [hz]
    exact Finset.sum_pos (fun _ _ => h₁ _ _) Finset.univ_nonempty
  have hrec : ∀ t a, z (t + 1) a = (∑ b, z t b * (ℙ[π]((y (t + 1)) = a | (y t) = b) : ℝ)) * (ℙ[π]((x (t + 1)) = xo (t + 1) | (y (t + 1)) = a) : ℝ) := by
    intro t a
    rw [hz, Fintype.sum_snoc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hz, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ys1 _ => ?_
    rw [(h₀ _).2 t, hpre t _ _ fun i hi => dite_snoc_eq ys1 b a hi]
    rw [dif_neg (lt_irrefl (t + 1)), dif_pos (Nat.lt_succ_self t), Fin.snoc_mk_last]
    ring
  refine ⟨fun t a => ?_, fun ys => ?_⟩
  ·
    have : Nonempty Y := ⟨a⟩
    have hs : (x' t + G a).exp.sum = ∑ b, z t b * (ℙ[π]((y (t + 1)) = a | (y t) = b) : ℝ) :=
      Finset.sum_congr rfl fun b _ => by show Real.exp (x' t b + G a b) = _; rw [Real.exp_add, h₆, hGt t a b, Real.exp_log (hzpos t b), Real.exp_log (hTt t a b)]
    rw [h₆, hrec, Real.log_mul (Finset.sum_pos (fun b _ => mul_pos (hzpos t b) (hTt t a b)) Finset.univ_nonempty).ne' (hE _ a).ne', hs, h₃]
  ·
    have : Nonempty Y := ⟨ys 0⟩
    have pad : ∀ (k : ℕ) (c : Y) (w : Fin k → Y), ((fun i : ℕ => if h : i < k then w ⟨i, h⟩ else c)[:k] : Fin k → Y) = w := by
      intro k c w
      funext i
      show (if h : i.val + 0 < k then w ⟨i.val + 0, h⟩ else c) = w i
      simp
    have e : ∀ ys' : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = ys') : ℝ) = P m (fun i => if h : i < m + 1 then ys' ⟨i, h⟩ else ys 0) := by
      intro ys'
      rw [hPdef]
      exact congrArg (fun w => (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = w) : ℝ)) (pad (m + 1) (ys 0) ys').symm
    have hD : ∑ ys' : Fin (m + 1) → Y, P m (fun i => if h : i < m + 1 then ys' ⟨i, h⟩ else ys 0) = (x' m).exp.sum := by
      rw [Function.sum_eq, Fintype.sum_snoc]
      refine Finset.sum_congr rfl fun b _ => ?_
      show _ = Real.exp (x' m b)
      rw [h₆, Real.exp_log (hzpos m b), hz]
      exact Finset.sum_congr rfl fun ys0 _ => hpre m _ _ fun i hi => dite_snoc_eq ys0 b (ys 0) hi
    have hDpos : 0 < (x' m).exp.sum := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
    have hnum : (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = ys[:m + 1]) : ℝ) = P m ys := (hPdef m ys).symm
    -- Bayes: Pr(y | x) = Pr(x ∧ y) / Pr(x), with Pr(x) = ∑ over the finite label space (total probability)
    have hrefXY : ReferenceMeasure.measure (α := (Fin (m + 1) → X) × (Fin (m + 1) → Y)) = Measure.count := by
      change (Measure.count : Measure (Fin (m + 1) → X)).prod (Measure.count : Measure (Fin (m + 1) → Y)) = Measure.count
      rw [← Count.eq.ProdCountS]
    have hrefYX : ReferenceMeasure.measure (α := (Fin (m + 1) → Y) × (Fin (m + 1) → X)) = Measure.count := by
      change (Measure.count : Measure (Fin (m + 1) → Y)).prod (Measure.count : Measure (Fin (m + 1) → X)) = Measure.count
      rw [← Count.eq.ProdCountS]
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
    have hden : ∑ b : Fin (m + 1) → Y, (ℙ[π](y[:m + 1] = b ∧ x[:m + 1] = xo[:m + 1]) : ENNReal) = (π.map (fun ω => ((y[:m + 1], x[:m + 1]) ω).2)).rnDeriv ReferenceMeasure.measure (xo[:m + 1]) := by
      have := Sum.eq.Prob (π := π) (x := y[:m + 1]) (y := x[:m + 1]) hYX rfl rfl (xo[:m + 1])
      rwa [tsum_fintype] at this
    have h₇ : (ℙ[π](y[:m + 1] = ys[:m + 1] | x[:m + 1] = xo[:m + 1]) : ℝ) = (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = ys[:m + 1]) : ℝ) / ∑ ys' : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = ys') : ℝ) := by
      have hfin : ∀ b : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = b) : ENNReal) ≠ ⊤ := fun b => by
        rw [hmXY]; exact measure_ne_top _ _
      have hc : (ℙ[π](y[:m + 1] = ys[:m + 1] | x[:m + 1] = xo[:m + 1]) : ENNReal) = (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = ys[:m + 1]) : ENNReal) / ∑ b : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = b) : ENNReal) := by
        unfold Measure.condProb
        rw [← hden, hmYX, ← hmXY]
        congr 1
        exact Finset.sum_congr rfl fun b _ => by rw [hmYX, hmXY]
      show ((ℙ[π](y[:m + 1] = ys[:m + 1] | x[:m + 1] = xo[:m + 1]) : ENNReal)).toReal = _
      rw [hc, ENNReal.toReal_div, ENNReal.toReal_sum fun b _ => hfin b]
    rw [h₇, Finset.sum_congr rfl (fun ys' _ => e ys'), hD, hnum, Real.log_div (h₁ _ _).ne' hDpos.ne', ← h₂]
    ring


-- created on 2018-12-21
-- updated on 2025-04-20
