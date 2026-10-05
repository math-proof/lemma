import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.Measure.eq.Mul_MulDivS.of.Subset
import Lemma.Random.MulMeasure.eq.MulMeasure.of.CondIndep
import Lemma.Random.Prob.eq.Measure.of.Eq_Count
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import sympy.stats.hidden_markov_sequence
import sympy.stats.discrete_hmm
import sympy.Basic
open MeasureTheory


/--
One-step factorization of the prefix probabilities of a hidden Markov sequence.
Let `x i` be the observations and `y i` the hidden labels (discrete, counting reference measures),
with, for every `t`, the emission independence `x (t + 1) ⟂ (x[:t + 1], y[:t + 1]) | y (t + 1)` and the
first-order Markov property `y (t + 1) ⟂ (x[:t + 1], y[:t]) | y t`.  Then for the fixed observed values
`xo` and any label sequence `ys`

  `Pr(x[:1] = xo[:1], y[:1] = ys[:1]) = Pr(x[0] = xo[0] | y[0] = ys[0]) * Pr(y[0] = ys[0])`,
  `Pr(x[:t+2] = xo[:t+2], y[:t+2] = ys[:t+2]) = Pr(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])
      * (Pr(y[t+1] = ys[t+1] | y[t] = ys[t]) * Pr(x[t+1] = xo[t+1] | y[t+1] = ys[t+1]))`.

No non-vanishing assumption is needed: when a conditioning event is null, both sides vanish.
-/
@[main]
private lemma main
  {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {xo : ℕ → X}
  [∀ i, SinglePSpace π (y i)]
  [∀ i j, SinglePSpace π (y i, y j)]
-- given
  (h : IsDiscreteHMM π x y)
  (ys : ℕ → Y) :
-- imply
  ℙ[π](x[:0 + 1] = xo[:0 + 1] ∧ y[:0 + 1] = ys[:0 + 1]) =
      ℙ[π]((x 0) = xo 0 | (y 0) = ys 0) * ℙ[π]((y 0) = ys 0) ∧
    ∀ t : ℕ, ℙ[π](x[:t + 1 + 1] = xo[:t + 1 + 1] ∧ y[:t + 1 + 1] = ys[:t + 1 + 1]) =
      ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) *
        (ℙ[π]((y (t + 1)) = ys (t + 1) | (y t) = ys t) *
          ℙ[π]((x (t + 1)) = xo (t + 1) | (y (t + 1)) = ys (t + 1))) := by
-- proof
  have ⟨hx, hy, hX, hY, h_emit, h_markov⟩ := h
  have : Nonempty X := ⟨xo 0⟩
  have : Nonempty Y := ⟨ys 0⟩
  have hpair : ∀ m n : ℕ, ReferenceMeasure.measure (α := (Fin m → X) × (Fin n → Y)) = Measure.count := fun m n => by
    change (Measure.count : Measure (Fin m → X)).prod Measure.count = Measure.count
    rw [← Measure.Count.eq.ProdCountS]
  have hP : ∀ a b : ℕ, (x[:(a : ℤ)], y[:(b : ℤ)]) ⁻¹' {(xo[:(a : ℤ)], ys[:(b : ℤ)])} =
      {ω | (∀ i < a, x i ω = xo i) ∧ ∀ i < b, y i ω = ys i} := by
    intro a b
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, JointRandomSymbol, Prod.mk.injEq, funext_iff]
    constructor
    · intro h
      exact ⟨fun i hi => h.1 ⟨i, hi⟩, fun i hi => h.2 ⟨i, hi⟩⟩
    · intro h
      exact ⟨fun i => h.1 i i.2, fun i => h.2 i i.2⟩
  have hJ : ∀ a b : ℕ, Measurable (x[:(a : ℤ)], y[:(b : ℤ)]) := fun a b =>
    (measurable_pi_lambda _ fun i => hx _).prodMk (measurable_pi_lambda _ fun i => hy _)
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → Set Ω, ∀ n, P n = {ω | (∀ i < n, x i ω = xo i) ∧ ∀ i < n, y i ω = ys i} :=
    ⟨_, fun _ => rfl⟩
  have hQ : ∀ n : ℕ, ℙ[π](x[:(n : ℤ)] = xo[:(n : ℤ)] ∧ y[:(n : ℤ)] = ys[:(n : ℤ)]) = π (P n) := by
    intro n
    rw [Random.Prob.eq.Measure.of.Eq_Count (hpair _ _), hP, hPdef]
  have hprob : ∀ i, ℙ[π]((y i) = ys i) = π (y i ⁻¹' {ys i}) := fun i =>
    Random.Prob.eq.Measure.of.Eq_Count hY _
  have hcondx : ∀ i j, ℙ[π]((x i) = xo i | (y j) = ys j) =
      π (x i ⁻¹' {xo i} ∩ y j ⁻¹' {ys j}) / π (y j ⁻¹' {ys j}) := fun i j =>
    Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count hX hY _ _
  have hcondy : ∀ i j, ℙ[π]((y i) = ys i | (y j) = ys j) =
      π (y i ⁻¹' {ys i} ∩ y j ⁻¹' {ys j}) / π (y j ⁻¹' {ys j}) := fun i j =>
    Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count hY hY _ _
  have key : ∀ (p : ℕ → Prop) (m : ℕ), (∀ i < m + 1, p i) ↔ (∀ i < m, p i) ∧ p m := fun p m =>
    ⟨fun h => ⟨fun i hi => h i (by omega), h m (by omega)⟩, fun h i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
      · exact h.1 i h'
      · exact h.2⟩
  refine ⟨?_, fun t => ?_⟩
  · refine (hQ 1).trans ?_
    rw [hcondx 0 0, hprob 0]
    have e : P 1 = x 0 ⁻¹' {xo 0} ∩ y 0 ⁻¹' {ys 0} := by
      ext ω
      simp [hPdef]
    rw [e]
    if h0 : π (y 0 ⁻¹' {ys 0}) = 0 then
      have : π (x 0 ⁻¹' {xo 0} ∩ y 0 ⁻¹' {ys 0}) = 0 := measure_mono_null Set.inter_subset_right h0
      rw [this, h0]
      simp
    else
      rw [ENNReal.div_mul_cancel h0 (measure_ne_top _ _)]
  · have hC : P (t + 1) ⊆ y t ⁻¹' {ys t} := by
      intro ω hω
      rw [hPdef] at hω
      exact hω.2 t (Nat.lt_succ_self t)
    have hset : P (t + 1 + 1) = P (t + 1) ∩ y (t + 1) ⁻¹' {ys (t + 1)} ∩ x (t + 1) ⁻¹' {xo (t + 1)} := by
      ext ω
      simp only [hPdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => x i ω = xo i), key (fun i => y i ω = ys i)]
      tauto
    have hJP : (x[:t + 1], y[:t + 1]) ⁻¹' {(xo[:t + 1], ys[:t + 1])} = P (t + 1) :=
      (hP (t + 1) (t + 1)).trans (hPdef _).symm
    have hJ₁ : Measurable (x[:t + 1], y[:t + 1]) := hJ (t + 1) (t + 1)
    have h₁ := Random.MulMeasure.eq.MulMeasure.of.CondIndep (hx (t + 1)) hJ₁ (hy (t + 1)) hX (hpair _ _) hY
      (h_emit t (hy (t + 1))) (xo (t + 1)) (xo[:t + 1], ys[:t + 1]) (ys (t + 1))
    rw [hJP] at h₁
    have hJP₂ : (x[:t + 1], y[:t]) ⁻¹' {(xo[:t + 1], ys[:t])} =
        {ω | (∀ i < t + 1, x i ω = xo i) ∧ ∀ i < t, y i ω = ys i} := hP (t + 1) t
    have hJ₂ : Measurable (x[:t + 1], y[:t]) := hJ (t + 1) t
    have h₂ := Random.MulMeasure.eq.MulMeasure.of.CondIndep (hy (t + 1)) hJ₂ (hy t) hY (hpair _ _) hY
      (h_markov t (hy t)) (ys (t + 1)) (xo[:t + 1], ys[:t]) (ys t)
    have e₂ : {ω | (∀ i < t + 1, x i ω = xo i) ∧ ∀ i < t, y i ω = ys i} ∩ y t ⁻¹' {ys t} = P (t + 1) := by
      ext ω
      simp only [hPdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => y i ω = ys i)]
      tauto
    have e₁ : y (t + 1) ⁻¹' {ys (t + 1)} ∩ {ω | (∀ i < t + 1, x i ω = xo i) ∧ ∀ i < t, y i ω = ys i} ∩ y t ⁻¹' {ys t} =
        y (t + 1) ⁻¹' {ys (t + 1)} ∩ P (t + 1) := by
      rw [Set.inter_assoc, e₂]
    rw [hJP₂, e₁, e₂] at h₂
    have h := Random.Measure.eq.Mul_MulDivS.of.Subset hC h₁ h₂
    rw [show ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) = π (P (t + 1)) from hQ (t + 1)]
    refine (hQ (t + 1 + 1)).trans ?_
    rw [hcondy (t + 1) t, hcondx (t + 1) (t + 1), hset]
    exact h


-- created on 2026-10-02
