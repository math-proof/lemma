import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Lemma.Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
import Lemma.Random.Measure.eq.Mul_MulDivS.of.Subset
import Lemma.Random.MulMeasure.eq.MulMeasure.of.CondIndep
import Lemma.Random.Prob.eq.Measure.of.Eq_Count
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import sympy.stats.hidden_markov_sequence
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure S] [ReferenceMeasure A]
  [Countable S] [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S} {a : ℕ → Ω → A} {«s.bvar» : ℕ → S} {«a.bvar» : ℕ → A}
-- given
  (hs : ∀ k, Measurable (s k))
  (ha : ∀ k, Measurable (a k))
  (hS : ReferenceMeasure.measure (α := S) = Measure.count)
  (hA : ReferenceMeasure.measure (α := A) = Measure.count)
  (hpol : ∀ t, ∀ _ : Measurable (s t),
    a t ⟂ᵢ[π] (s[:t], a[:t]) | s t)
  (htrans : ∀ t, ∀ _ : Measurable (s t, a t),
    s (t + 1) ⟂ᵢ[π] (s[:t], a[:t]) | (s t, a t)) :
-- imply
  have : ∀ i, SinglePSpace π (s i) := fun i =>
    Random.SinglePSpace.of.EqMeasureCount.Measurable (hs i) hS
  have : ∀ i j, SinglePSpace π (a i, s j) := fun i j =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (ha i) (hs j) hA hS
  have : ∀ i, SinglePSpace π (s (i + 1), s i, a i) := fun i =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (hs (i + 1)) ((hs i).prodMk (ha i)) hS (by
      change (ReferenceMeasure.measure (α := S)).prod ReferenceMeasure.measure = Measure.count
      rw [hS, hA, ← Measure.Count.eq.ProdCountS])
  have : ∀ n, SinglePSpace π (s[:n + 1], a[:n]) := fun n =>
    Random.SinglePSpace.of.All_Measurable.All_Measurable hs ha
  ℙ[π](s[:0 + 1] = «s.bvar»[:0 + 1] ∧ a[:0] = «a.bvar»[:0]) = ℙ[π]((s 0) = «s.bvar» 0) ∧
    ∀ t : ℕ, ℙ[π](s[:t + 1 + 1] = «s.bvar»[:t + 1 + 1] ∧ a[:t + 1] = «a.bvar»[:t + 1]) =
      ℙ[π](s[:t + 1] = «s.bvar»[:t + 1] ∧ a[:t] = «a.bvar»[:t]) *
        (ℙ[π]((a t) = «a.bvar» t | (s t) = «s.bvar» t) *
          ℙ[π]((s (t + 1)) = «s.bvar» (t + 1) | (s t) = «s.bvar» t ∧ (a t) = «a.bvar» t)) := by
-- proof
  intro _ _ _ _
  have : Nonempty S := ⟨«s.bvar» 0⟩
  have : Nonempty A := ⟨«a.bvar» 0⟩
  have hpair : ∀ p q : ℕ, ReferenceMeasure.measure (α := (Fin p → S) × (Fin q → A)) = Measure.count := fun p q => by
    change (Measure.count : Measure (Fin p → S)).prod Measure.count = Measure.count
    rw [← Measure.Count.eq.ProdCountS]
  have hSA : ReferenceMeasure.measure (α := S × A) = Measure.count := by
    change (ReferenceMeasure.measure : Measure S).prod ReferenceMeasure.measure = Measure.count
    rw [hS, hA, ← Measure.Count.eq.ProdCountS]
  have hP : ∀ p q : ℕ, (s[:(p : ℤ)], a[:(q : ℤ)]) ⁻¹' {(«s.bvar»[:(p : ℤ)], «a.bvar»[:(q : ℤ)])} =
      {ω | (∀ i < p, s i ω = «s.bvar» i) ∧ ∀ i < q, a i ω = «a.bvar» i} := by
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
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ → Set Ω, ∀ n, Q n = {ω | (∀ i < n + 1, s i ω = «s.bvar» i) ∧ ∀ i < n, a i ω = «a.bvar» i} :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → Set Ω, ∀ n, H n = {ω | (∀ i < n, s i ω = «s.bvar» i) ∧ ∀ i < n, a i ω = «a.bvar» i} :=
    ⟨_, fun _ => rfl⟩
  have hQ : ∀ n : ℕ, ℙ[π](s[:(n : ℤ) + 1] = «s.bvar»[:(n : ℤ) + 1] ∧ a[:(n : ℤ)] = «a.bvar»[:(n : ℤ)]) = π (Q n) := by
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
  · have hZ : (s t, a t) ⁻¹' {(«s.bvar» t, «a.bvar» t)} = s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t} := by
      ext ω
      simp [JointRandomSymbol]
    have hZm : Measurable (s t, a t) := (hs t).prodMk (ha t)
    have hQH : Q t = H t ∩ s t ⁻¹' {«s.bvar» t} := by
      ext ω
      simp only [hQdef, hHdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => s i ω = «s.bvar» i)]
      tauto
    have hQQ : Q (t + 1) = Q t ∩ (s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t}) ∩ s (t + 1) ⁻¹' {«s.bvar» (t + 1)} := by
      ext ω
      simp only [hQdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => s i ω = «s.bvar» i) (t + 1), key (fun i => s i ω = «s.bvar» i) t, key (fun i => a i ω = «a.bvar» i) t]
      tauto
    have hHist : (s[:(t : ℤ)], a[:(t : ℤ)]) ⁻¹' {(«s.bvar»[:(t : ℤ)], «a.bvar»[:(t : ℤ)])} = H t := by
      rw [hP t t, hHdef]
    -- policy: `a t ⟂ history | s t`
    have hpol' := Random.MulMeasure.eq.MulMeasure.of.CondIndep (ha t) (hJ t t) (hs t) hA (hpair _ _) hS
      (hpol t (hs t)) («a.bvar» t) («s.bvar»[:(t : ℤ)], «a.bvar»[:(t : ℤ)]) («s.bvar» t)
    rw [hHist] at hpol'
    -- transition: `s (t + 1) ⟂ history | (s t, a t)`
    have htrans' := Random.MulMeasure.eq.MulMeasure.of.CondIndep (hs (t + 1)) (hJ t t) hZm hS (hpair _ _) hSA
      (htrans t hZm) («s.bvar» (t + 1)) («s.bvar»[:(t : ℤ)], «a.bvar»[:(t : ℤ)]) («s.bvar» t, «a.bvar» t)
    rw [hHist] at htrans'
    rw [hZ] at htrans'
    have hSsub : Q t ⊆ s t ⁻¹' {«s.bvar» t} := by
      rw [hQH]
      exact Set.inter_subset_right
    have h₁ : π (s (t + 1) ⁻¹' {«s.bvar» (t + 1)} ∩ Q t ∩ (s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t})) * π (s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t}) =
        π (s (t + 1) ⁻¹' {«s.bvar» (t + 1)} ∩ (s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t})) * π (Q t ∩ (s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t})) := by
      rw [hQH]
      convert htrans' using 3 <;>
      · ext ω
        simp only [Set.mem_inter_iff]
        tauto
    have h₂ : π ((s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t}) ∩ Q t) * π (s t ⁻¹' {«s.bvar» t}) =
        π ((s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t}) ∩ s t ⁻¹' {«s.bvar» t}) * π (Q t) := by
      rw [hQH]
      convert hpol' using 3 <;>
      · ext ω
        simp only [Set.mem_inter_iff]
        tauto
    have h := Random.Measure.eq.Mul_MulDivS.of.Subset hSsub h₁ h₂
    have hFS : (s t ⁻¹' {«s.bvar» t} ∩ a t ⁻¹' {«a.bvar» t}) ∩ s t ⁻¹' {«s.bvar» t} = a t ⁻¹' {«a.bvar» t} ∩ s t ⁻¹' {«s.bvar» t} := by
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [hFS] at h
    refine (hQ (t + 1)).trans ?_
    rw [hQ t, Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count hA hS, Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count hS hSA, hZ, hQQ]
    exact h


-- created on 2023-03-22
-- updated on 2023-05-17
