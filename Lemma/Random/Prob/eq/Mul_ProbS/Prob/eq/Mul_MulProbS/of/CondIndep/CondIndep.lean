import Lemma.Random.Measure.eq.Mul_MulDivS.of.Subset
import Lemma.Random.MulMeasure.eq.MulMeasure.of.CondIndep
import Lemma.Random.ProbCond.eq.Div.of.SinglePSpace
import sympy.stats.discrete_hmm
open MeasureTheory Random
open IsDiscreteHMM


/-- `f[i]` on a bare function. Local: a public `GetElem` would clash with Mathlib `P[X]`. -/
@[reducible]
local instance : GetElem (α → β) α β (fun _ _ => True) where
  getElem f i _ := f i

lemma fun_getElem (f : α → β) (i : α) : f[i] = f i := rfl

/--
One-step factorization of the prefix probabilities of a hidden Markov sequence.
Let `x[i]` be the observations and `y[i]` the hidden labels (discrete, counting reference measures),
with, for every `t`, the emission independence `x[t + 1] ⟂ (x[:t + 1], y[:t + 1]) | y[t + 1]` and the
first-order Markov property `y[t + 1] ⟂ (x[:t + 1], y[:t]) | y[t]`.  Then for the fixed observed values
`«x.bvar»` and any label sequence `«y.bvar»`

  `ℙ(x[:1] = «x.bvar»[:1], y[:1] = «y.bvar»[:1]) = ℙ(x[0] = «x.bvar»[0] | y[0] = «y.bvar»[0]) * ℙ(y[0] = «y.bvar»[0])`,
  `ℙ(x[:t+2] = «x.bvar»[:t+2], y[:t+2] = «y.bvar»[:t+2]) = ℙ(x[:t+1] = «x.bvar»[:t+1], y[:t+1] = «y.bvar»[:t+1])
      * (ℙ(y[t+1] = «y.bvar»[t+1] | y[t] = «y.bvar»[t]) * ℙ(x[t+1] = «x.bvar»[t+1] | y[t+1] = «y.bvar»[t+1]))`.

No non-vanishing assumption is needed: when a conditioning event is null, both sides vanish.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {«x.bvar» : ℕ → X}
-- given
  (h : IsDiscreteHMM π x y)
  («y.bvar» : ℕ → Y) :
-- imply
  ℙ[π](x[:0 + 1] = «x.bvar»[:0 + 1] ∧ y[:0 + 1] = «y.bvar»[:0 + 1]) =
      ℙ[π](x[0] = «x.bvar»[0] | y[0] = «y.bvar»[0]) * ℙ[π](y[0] = «y.bvar»[0]) ∧
    ∀ t : ℕ, ℙ[π](x[:t + 1 + 1] = «x.bvar»[:t + 1 + 1] ∧ y[:t + 1 + 1] = «y.bvar»[:t + 1 + 1]) =
      ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) *
        (ℙ[π](y[t + 1] = «y.bvar»[t + 1] | y[t] = «y.bvar»[t]) *
          ℙ[π](x[t + 1] = «x.bvar»[t + 1] | y[t + 1] = «y.bvar»[t + 1])) := by
-- proof
  have hx := h.measurable_x
  have hy := h.measurable_y
  have h_emit := h.emit
  have h_markov := h.markov
  have : Nonempty X := ⟨«x.bvar» 0⟩
  have : Nonempty Y := ⟨«y.bvar» 0⟩
  have hP : ∀ a b : ℕ, (x[:(a : ℤ)], y[:(b : ℤ)]) ⁻¹' {(«x.bvar»[:(a : ℤ)], «y.bvar»[:(b : ℤ)])} =
      {ω | (∀ i < a, x i ω = «x.bvar» i) ∧ ∀ i < b, y i ω = «y.bvar» i} := by
    intro a b
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, JointRandomSymbol, Prod.mk.injEq, funext_iff]
    constructor
    ·
      intro h
      exact ⟨fun i hi => h.1 ⟨i, hi⟩, fun i hi => h.2 ⟨i, hi⟩⟩
    ·
      intro h
      exact ⟨fun i => h.1 i i.2, fun i => h.2 i i.2⟩
  have hJ : ∀ a b : ℕ, Measurable (x[:(a : ℤ)], y[:(b : ℤ)]) := fun a b =>
    (Measurable.of_eval fun i => hx _).prodMk (Measurable.of_eval fun i => hy _)
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → Set Ω, ∀ n, P n = {ω | (∀ i < n, x i ω = «x.bvar» i) ∧ ∀ i < n, y i ω = «y.bvar» i} :=
    ⟨_, fun _ => rfl⟩
  have hQ : ∀ n : ℕ, ℙ[π](x[:(n : ℤ)] = «x.bvar»[:(n : ℤ)] ∧ y[:(n : ℤ)] = «y.bvar»[:(n : ℤ)]) = π (P n) := by
    intro n
    rw [EqProb, hP, hPdef]
  have hprob : ∀ i, ℙ[π](y[i] = «y.bvar»[i]) = π (y i ⁻¹' {«y.bvar» i}) := fun i =>
    EqProb _
  have hcondx : ∀ i j, ℙ[π](x[i] = «x.bvar»[i] | y[j] = «y.bvar»[j]) =
      π (x i ⁻¹' {«x.bvar» i} ∩ y j ⁻¹' {«y.bvar» j}) / π (y j ⁻¹' {«y.bvar» j}) := fun i j =>
    ProbCond.eq.Div.of.SinglePSpace inferInstance _ _
  have hcondy : ∀ i j, ℙ[π](y[i] = «y.bvar»[i] | y[j] = «y.bvar»[j]) =
      π (y i ⁻¹' {«y.bvar» i} ∩ y j ⁻¹' {«y.bvar» j}) / π (y j ⁻¹' {«y.bvar» j}) := fun i j =>
    ProbCond.eq.Div.of.SinglePSpace inferInstance _ _
  have key : ∀ (p : ℕ → Prop) (m : ℕ), (∀ i < m + 1, p i) ↔ (∀ i < m, p i) ∧ p m := fun p m =>
    ⟨fun h => ⟨fun i hi => h i (by omega), h m (by omega)⟩, fun h i hi => by
      obtain h' | rfl := Nat.lt_succ_iff_lt_or_eq.mp hi
      · exact h.1 i h'
      · exact h.2⟩
  refine ⟨?_, fun t => ?_⟩
  ·
    refine (hQ 1).trans ?_
    rw [hcondx 0 0, hprob 0]
    have e : P 1 = x 0 ⁻¹' {«x.bvar» 0} ∩ y 0 ⁻¹' {«y.bvar» 0} := by
      ext ω
      simp [hPdef]
    rw [e]
    if h0 : π (y 0 ⁻¹' {«y.bvar» 0}) = 0 then
      have : π (x 0 ⁻¹' {«x.bvar» 0} ∩ y 0 ⁻¹' {«y.bvar» 0}) = 0 := measure_mono_null Set.inter_subset_right h0
      rw [this, h0]
      simp
    else
      rw [ENNReal.div_mul_cancel h0 (measure_ne_top _ _)]
  ·
    have hC : P (t + 1) ⊆ y t ⁻¹' {«y.bvar» t} := by
      intro ω hω
      exact (hPdef _ ▸ hω).2 t (Nat.lt_succ_self t)
    have hset : P (t + 1 + 1) = P (t + 1) ∩ y (t + 1) ⁻¹' {«y.bvar» (t + 1)} ∩ x (t + 1) ⁻¹' {«x.bvar» (t + 1)} := by
      ext ω
      simp only [hPdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => x i ω = «x.bvar» i), key (fun i => y i ω = «y.bvar» i)]
      tauto
    have hJP : (x[:t + 1], y[:t + 1]) ⁻¹' {(«x.bvar»[:t + 1], «y.bvar»[:t + 1])} = P (t + 1) :=
      (hP (t + 1) (t + 1)).trans (hPdef _).symm
    have hJ₁ : Measurable (x[:t + 1], y[:t + 1]) := hJ (t + 1) (t + 1)
    have h₁ := MulMeasure.eq.MulMeasure.of.CondIndep (hx (t + 1)) hJ₁ (hy (t + 1))
      (h_emit t (hy (t + 1))) («x.bvar» (t + 1)) («x.bvar»[:t + 1], «y.bvar»[:t + 1]) («y.bvar» (t + 1))
    rw [hJP] at h₁
    have hJP₂ : (x[:t + 1], y[:t]) ⁻¹' {(«x.bvar»[:t + 1], «y.bvar»[:t])} =
        {ω | (∀ i < t + 1, x i ω = «x.bvar» i) ∧ ∀ i < t, y i ω = «y.bvar» i} := hP (t + 1) t
    have hJ₂ : Measurable (x[:t + 1], y[:t]) := hJ (t + 1) t
    have h₂ := MulMeasure.eq.MulMeasure.of.CondIndep (hy (t + 1)) hJ₂ (hy t)
      (h_markov t (hy t)) («y.bvar» (t + 1)) («x.bvar»[:t + 1], «y.bvar»[:t]) («y.bvar» t)
    have e₂ : {ω | (∀ i < t + 1, x i ω = «x.bvar» i) ∧ ∀ i < t, y i ω = «y.bvar» i} ∩ y t ⁻¹' {«y.bvar» t} = P (t + 1) := by
      ext ω
      simp only [hPdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => y i ω = «y.bvar» i)]
      tauto
    have e₁ : y (t + 1) ⁻¹' {«y.bvar» (t + 1)} ∩ {ω | (∀ i < t + 1, x i ω = «x.bvar» i) ∧ ∀ i < t, y i ω = «y.bvar» i} ∩ y t ⁻¹' {«y.bvar» t} =
        y (t + 1) ⁻¹' {«y.bvar» (t + 1)} ∩ P (t + 1) := by
      rw [Set.inter_assoc, e₂]
    rw [hJP₂, e₁, e₂] at h₂
    have h := Measure.eq.Mul_MulDivS.of.Subset hC h₁ h₂
    rw [show ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) = π (P (t + 1)) from hQ (t + 1)]
    refine (hQ (t + 1 + 1)).trans ?_
    rwa [hcondy (t + 1) t, hcondx (t + 1) (t + 1), hset]


-- created on 2026-10-02
-- updated on 2026-10-23
