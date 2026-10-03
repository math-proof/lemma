import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.Measure.eq.Mul_MulDivS.of.Subset
import Lemma.Random.MulMeasure.eq.MulMeasure.of.CondIndep
import Lemma.Random.Prob.eq.Measure.of.Eq_Count
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory


/--
One-step factorization of the prefix probabilities of a Markov decision process.
Let `s i` be the states and `a i` the actions (discrete, counting reference measures) on a probability
space, with, for every `t`, the policy property `a t ⟂ (s[:t], a[:t]) | s t` (the action depends on the
history only through the current state) and the transition property
`s (t + 1) ⟂ (s[:t], a[:t]) | (s t, a t)`.  Then for the fixed values `sv` and `av`

  `Pr(s[:1] = sv[:1], a[:0] = av[:0]) = Pr(s[0] = sv[0])`,
  `Pr(s[:t+2] = sv[:t+2], a[:t+1] = av[:t+1]) = Pr(s[:t+1] = sv[:t+1], a[:t] = av[:t])
      * (Pr(a[t] = av[t] | s[t] = sv[t]) * Pr(s[t+1] = sv[t+1] | s[t] = sv[t] ∧ a[t] = av[t]))`.

No non-vanishing assumption is needed: when a conditioning event is null, both sides vanish.
(The py lemma `Random.Eq.of.Ne_0.Eq.Eq.Eq.markov.decision` states these properties marginally,
`s[k + 1] | s[:k] & a[:k] = s[k + 1]`; that is too weak for the factorization, so the conditional
form is used here.)
-/
@[main]
private lemma main
  {Ω S A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure S] [ReferenceMeasure A]
  [Countable S] [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S} {a : ℕ → Ω → A} {sv : ℕ → S} {av : ℕ → A}
  [∀ i, SinglePSpace π (s i)]
  [∀ i j, SinglePSpace π (a i, s j)]
  [∀ i, SinglePSpace π (JointRandomSymbol (s (i + 1)) (JointRandomSymbol (s i) (a i)))]
  [∀ n, SinglePSpace π (s[:n + 1], a[:n])]
-- given
  (hs : ∀ k, Measurable (s k))
  (ha : ∀ k, Measurable (a k))
  (hS : ReferenceMeasure.measure (α := S) = Measure.count)
  (hA : ReferenceMeasure.measure (α := A) = Measure.count)
  (hpol : ∀ t, ∀ _ : Measurable (s t),
    a t ⟂ᵢ[π] (s[:t], a[:t]) | s t)
  (htrans : ∀ t, ∀ _ : Measurable (JointRandomSymbol (s t) (a t)),
    s (t + 1) ⟂ᵢ[π] (s[:t], a[:t]) | JointRandomSymbol (s t) (a t)) :
-- imply
  ℙ[π](s[:0 + 1] = sv[:0 + 1] ∧ a[:0] = av[:0]) = ℙ[π]((s 0) = sv 0) ∧
    ∀ t : ℕ, ℙ[π](s[:t + 1 + 1] = sv[:t + 1 + 1] ∧ a[:t + 1] = av[:t + 1]) =
      ℙ[π](s[:t + 1] = sv[:t + 1] ∧ a[:t] = av[:t]) *
        (ℙ[π]((a t) = av t | (s t) = sv t) *
          ℙ[π]((s (t + 1)) = sv (t + 1) | (s t) = sv t ∧ (a t) = av t)) := by
-- proof
  have : Nonempty S := ⟨sv 0⟩
  have : Nonempty A := ⟨av 0⟩
  have hpair : ∀ p q : ℕ, ReferenceMeasure.measure (α := (Fin p → S) × (Fin q → A)) = Measure.count := fun p q => by
    change (Measure.count : Measure (Fin p → S)).prod Measure.count = Measure.count
    rw [← Measure.Count.eq.ProdCountS]
  have hSA : ReferenceMeasure.measure (α := S × A) = Measure.count := by
    change (ReferenceMeasure.measure : Measure S).prod ReferenceMeasure.measure = Measure.count
    rw [hS, hA, ← Measure.Count.eq.ProdCountS]
  have hP : ∀ p q : ℕ, (s[:(p : ℤ)], a[:(q : ℤ)]) ⁻¹' {(sv[:(p : ℤ)], av[:(q : ℤ)])} =
      {ω | (∀ i < p, s i ω = sv i) ∧ ∀ i < q, a i ω = av i} := by
    intro p q
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, JointRandomSymbol, Prod.mk.injEq, funext_iff]
    constructor
    · intro h
      exact ⟨fun i hi => h.1 ⟨i, hi⟩, fun i hi => h.2 ⟨i, hi⟩⟩
    · intro h
      exact ⟨fun i => h.1 i i.2, fun i => h.2 i i.2⟩
  have hJ : ∀ p q : ℕ, Measurable (s[:(p : ℤ)], a[:(q : ℤ)]) := fun p q =>
    (measurable_pi_lambda _ fun i => hs _).prodMk (measurable_pi_lambda _ fun i => ha _)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ → Set Ω, ∀ n, Q n = {ω | (∀ i < n + 1, s i ω = sv i) ∧ ∀ i < n, a i ω = av i} :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → Set Ω, ∀ n, H n = {ω | (∀ i < n, s i ω = sv i) ∧ ∀ i < n, a i ω = av i} :=
    ⟨_, fun _ => rfl⟩
  have hQ : ∀ n : ℕ, ℙ[π](s[:(n : ℤ) + 1] = sv[:(n : ℤ) + 1] ∧ a[:(n : ℤ)] = av[:(n : ℤ)]) = π (Q n) := by
    intro n
    rw [Random.Prob.eq.Measure.of.Eq_Count (hpair _ _), hQdef]
    exact congrArg π (hP (n + 1) n)
  have key : ∀ (p : ℕ → Prop) (m : ℕ), (∀ i < m + 1, p i) ↔ (∀ i < m, p i) ∧ p m := fun p m =>
    ⟨fun h => ⟨fun i hi => h i (by omega), h m (by omega)⟩, fun h i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
      · exact h.1 i h'
      · exact h.2⟩
  refine ⟨?_, fun t => ?_⟩
  · refine (hQ 0).trans ?_
    rw [Random.Prob.eq.Measure.of.Eq_Count hS]
    congr 1
    ext ω
    simp [hQdef]
  · have hZ : (JointRandomSymbol (s t) (a t)) ⁻¹' {(sv t, av t)} = s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t} := by
      ext ω
      simp [JointRandomSymbol]
    have hZm : Measurable (JointRandomSymbol (s t) (a t)) := (hs t).prodMk (ha t)
    have hQH : Q t = H t ∩ s t ⁻¹' {sv t} := by
      ext ω
      simp only [hQdef, hHdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => s i ω = sv i)]
      tauto
    have hQQ : Q (t + 1) = Q t ∩ (s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t}) ∩ s (t + 1) ⁻¹' {sv (t + 1)} := by
      ext ω
      simp only [hQdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => s i ω = sv i) (t + 1), key (fun i => s i ω = sv i) t, key (fun i => a i ω = av i) t]
      tauto
    have hHist : (s[:(t : ℤ)], a[:(t : ℤ)]) ⁻¹' {(sv[:(t : ℤ)], av[:(t : ℤ)])} = H t := by
      rw [hP t t, hHdef]
    -- policy: `a t ⟂ history | s t`
    have hpol' := Random.MulMeasure.eq.MulMeasure.of.CondIndep (ha t) (hJ t t) (hs t) hA (hpair _ _) hS
      (hpol t (hs t)) (av t) (sv[:(t : ℤ)], av[:(t : ℤ)]) (sv t)
    rw [hHist] at hpol'
    -- transition: `s (t + 1) ⟂ history | (s t, a t)`
    have htrans' := Random.MulMeasure.eq.MulMeasure.of.CondIndep (hs (t + 1)) (hJ t t) hZm hS (hpair _ _) hSA
      (htrans t hZm) (sv (t + 1)) (sv[:(t : ℤ)], av[:(t : ℤ)]) (sv t, av t)
    rw [hHist] at htrans'
    rw [hZ] at htrans'
    have hSsub : Q t ⊆ s t ⁻¹' {sv t} := by
      rw [hQH]
      exact Set.inter_subset_right
    have h₁ : π (s (t + 1) ⁻¹' {sv (t + 1)} ∩ Q t ∩ (s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t})) * π (s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t}) =
        π (s (t + 1) ⁻¹' {sv (t + 1)} ∩ (s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t})) * π (Q t ∩ (s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t})) := by
      rw [hQH]
      convert htrans' using 3 <;>
      · ext ω
        simp only [Set.mem_inter_iff]
        tauto
    have h₂ : π ((s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t}) ∩ Q t) * π (s t ⁻¹' {sv t}) =
        π ((s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t}) ∩ s t ⁻¹' {sv t}) * π (Q t) := by
      rw [hQH]
      convert hpol' using 3 <;>
      · ext ω
        simp only [Set.mem_inter_iff]
        tauto
    have h := Random.Measure.eq.Mul_MulDivS.of.Subset hSsub h₁ h₂
    have hFS : (s t ⁻¹' {sv t} ∩ a t ⁻¹' {av t}) ∩ s t ⁻¹' {sv t} = a t ⁻¹' {av t} ∩ s t ⁻¹' {sv t} := by
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [hFS] at h
    refine (hQ (t + 1)).trans ?_
    rw [hQ t, Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count hA hS, Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count hS hSA, hZ, hQQ]
    exact h


-- created on 2023-03-22
-- updated on 2023-05-17