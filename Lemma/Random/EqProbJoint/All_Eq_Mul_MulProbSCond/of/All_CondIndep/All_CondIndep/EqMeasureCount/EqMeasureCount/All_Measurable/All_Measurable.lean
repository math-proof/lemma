import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Lemma.Random.Measure.eq.Mul_MulDivS.of.Subset
import Lemma.Random.MulMeasure.eq.MulMeasure.of.CondIndep
open MeasureTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure S] [CountableMeasure A]
  [Countable S] [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S} {a : ℕ → Ω → A} {«\sf{s}» : ℕ → S} {«\sf{a}» : ℕ → A}
-- given
  (hs : ∀ k, Measurable (s k))
  (ha : ∀ k, Measurable (a k))
  (hpol : ∀ t, ∀ _ : Measurable (s t),
    a t ⟂ᵢ[π] (s[:t], a[:t]) | s t)
  (htrans : ∀ t, ∀ _ : Measurable (s t, a t),
    s (t + 1) ⟂ᵢ[π] (s[:t], a[:t]) | (s t, a t)) :
-- imply
  have : ∀ i, SinglePSpace π (s i) := fun i =>
    SinglePSpace.of.Measurable (hs i)
  have : ∀ i j, SinglePSpace π (a i, s j) := fun i j =>
    SinglePSpace.of.Measurable.Measurable (ha i) (hs j)
  have : ∀ i, SinglePSpace π (s (i + 1), s i, a i) := fun i =>
    SinglePSpace.of.Measurable.Measurable (hs (i + 1)) ((hs i).prodMk (ha i))
  have : ∀ n, SinglePSpace π (s[:n + 1], a[:n]) := fun _ =>
    SinglePSpace.of.All_Measurable.All_Measurable hs ha
  ℙ[π](s[:0 + 1] = «\sf{s}»[:0 + 1] ∧ a[:0] = «\sf{a}»[:0]) = ℙ[π]((s 0) = «\sf{s}» 0) ∧
    ∀ t : ℕ, ℙ[π](s[:t + 1 + 1] = «\sf{s}»[:t + 1 + 1] ∧ a[:t + 1] = «\sf{a}»[:t + 1]) =
      ℙ[π](s[:t + 1] = «\sf{s}»[:t + 1] ∧ a[:t] = «\sf{a}»[:t]) *
        (ℙ[π]((a t) = «\sf{a}» t | (s t) = «\sf{s}» t) *
          ℙ[π]((s (t + 1)) = «\sf{s}» (t + 1) | (s t) = «\sf{s}» t ∧ (a t) = «\sf{a}» t)) := by
-- proof
  intro _ _ _ _
  have : Nonempty S := ⟨«\sf{s}» 0⟩
  have : Nonempty A := ⟨«\sf{a}» 0⟩
  have hP : ∀ p q : ℕ, (s[:(p : ℤ)], a[:(q : ℤ)]) ⁻¹' {(«\sf{s}»[:(p : ℤ)], «\sf{a}»[:(q : ℤ)])} =
      {ω | (∀ i < p, s i ω = «\sf{s}» i) ∧ ∀ i < q, a i ω = «\sf{a}» i} := by
    intro p q
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, JointRandomSymbol, Prod.mk.injEq, funext_iff]
    constructor
    ·
      intro h
      exact ⟨fun i hi => h.1 ⟨i, hi⟩, fun i hi => h.2 ⟨i, hi⟩⟩
    ·
      intro h
      exact ⟨fun i => h.1 i i.2, fun i => h.2 i i.2⟩
  have hJ : ∀ p q : ℕ, Measurable (s[:(p : ℤ)], a[:(q : ℤ)]) := fun p q =>
    (Measurable.of_eval fun i => hs _).prodMk (Measurable.of_eval fun i => ha _)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ → Set Ω, ∀ n, Q n = {ω | (∀ i < n + 1, s i ω = «\sf{s}» i) ∧ ∀ i < n, a i ω = «\sf{a}» i} :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → Set Ω, ∀ n, H n = {ω | (∀ i < n, s i ω = «\sf{s}» i) ∧ ∀ i < n, a i ω = «\sf{a}» i} :=
    ⟨_, fun _ => rfl⟩
  have hQ : ∀ n : ℕ, ℙ[π](s[:(n : ℤ) + 1] = «\sf{s}»[:(n : ℤ) + 1] ∧ a[:(n : ℤ)] = «\sf{a}»[:(n : ℤ)]) = π (Q n) := by
    intro n
    rw [EqProb, hQdef]
    exact congrArg π (hP (n + 1) n)
  have key : ∀ (p : ℕ → Prop) (m : ℕ), (∀ i < m + 1, p i) ↔ (∀ i < m, p i) ∧ p m := fun p m =>
    ⟨fun h => ⟨fun i hi => h i (by omega), h m (by omega)⟩, fun h i hi => by
      obtain h' | rfl := Nat.lt_succ_iff_lt_or_eq.mp hi
      · exact h.1 i h'
      · exact h.2⟩
  refine ⟨?_, fun t => ?_⟩
  ·
    refine (hQ 0).trans ?_
    rw [EqProb]
    congr 1
    ext ω
    simp [hQdef]
  ·
    have hZ : (s t, a t) ⁻¹' {(«\sf{s}» t, «\sf{a}» t)} = s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t} := by
      ext ω
      simp [JointRandomSymbol]
    have hZm : Measurable (s t, a t) := (hs t).prodMk (ha t)
    have hQH : Q t = H t ∩ s t ⁻¹' {«\sf{s}» t} := by
      ext ω
      simp only [hQdef, hHdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => s i ω = «\sf{s}» i)]
      tauto
    have hQQ : Q (t + 1) = Q t ∩ (s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t}) ∩ s (t + 1) ⁻¹' {«\sf{s}» (t + 1)} := by
      ext ω
      simp only [hQdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [key (fun i => s i ω = «\sf{s}» i) (t + 1), key (fun i => s i ω = «\sf{s}» i) t, key (fun i => a i ω = «\sf{a}» i) t]
      tauto
    have hHist : (s[:(t : ℤ)], a[:(t : ℤ)]) ⁻¹' {(«\sf{s}»[:(t : ℤ)], «\sf{a}»[:(t : ℤ)])} = H t := by
      rw [hP t t, hHdef]
    -- policy: `a t ⟂ history | s t`
    have hpol' := MulMeasure.eq.MulMeasure.of.CondIndep (ha t) (hJ t t) (hs t)
      (hpol t (hs t)) («\sf{a}» t) («\sf{s}»[:(t : ℤ)], «\sf{a}»[:(t : ℤ)]) («\sf{s}» t)
    rw [hHist] at hpol'
    -- transition: `s (t + 1) ⟂ history | (s t, a t)`
    have htrans' := MulMeasure.eq.MulMeasure.of.CondIndep (hs (t + 1)) (hJ t t) hZm
      (htrans t hZm) («\sf{s}» (t + 1)) («\sf{s}»[:(t : ℤ)], «\sf{a}»[:(t : ℤ)]) («\sf{s}» t, «\sf{a}» t)
    rw [hHist] at htrans'
    rw [hZ] at htrans'
    have hSsub : Q t ⊆ s t ⁻¹' {«\sf{s}» t} :=
      hQH ▸ Set.inter_subset_right
    have h₁ : π (s (t + 1) ⁻¹' {«\sf{s}» (t + 1)} ∩ Q t ∩ (s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t})) * π (s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t}) =
        π (s (t + 1) ⁻¹' {«\sf{s}» (t + 1)} ∩ (s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t})) * π (Q t ∩ (s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t})) := by
      rw [hQH]
      convert htrans' using 3 <;>
      ·
        ext ω
        simp only [Set.mem_inter_iff]
        tauto
    have h₂ : π ((s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t}) ∩ Q t) * π (s t ⁻¹' {«\sf{s}» t}) =
        π ((s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t}) ∩ s t ⁻¹' {«\sf{s}» t}) * π (Q t) := by
      rw [hQH]
      convert hpol' using 3 <;>
      ·
        ext ω
        simp only [Set.mem_inter_iff]
        tauto
    have h := Measure.eq.Mul_MulDivS.of.Subset hSsub h₁ h₂
    have hFS : (s t ⁻¹' {«\sf{s}» t} ∩ a t ⁻¹' {«\sf{a}» t}) ∩ s t ⁻¹' {«\sf{s}» t} = a t ⁻¹' {«\sf{a}» t} ∩ s t ⁻¹' {«\sf{s}» t} := by
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [hFS] at h
    refine (hQ (t + 1)).trans ?_
    rwa [hQ t, Prob_Cond.eq.Div.of.SinglePSpace inferInstance, Prob_Cond.eq.Div.of.SinglePSpace inferInstance, hZ, hQQ]


-- created on 2023-03-22
-- updated on 2026-11-02
