import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.Prob.eq.Measure.of.Eq_Count
import Lemma.Random.MulMeasure.eq.MulMeasure.of.CondIndep
import Lemma.Random.Measure.eq.Mul_MulDivS.of.Subset
import sympy.stats.discrete_hmm
import sympy.concrete.summations
import sympy.Basic
open MeasureTheory
open IsDiscreteHMM


/--
Likelihood of an observed sequence in a hidden Markov model, cut at any time `t`.
Let `x` (observations) and `y` (hidden states) form a discrete HMM `IsDiscreteHMM π x y` with finitely many
states, let `«x.bvar»` be a fixed observed sequence and let `n` be the number of time steps.  Splitting the
observations at any time `t : Fin n` into the past `x[:t + 1]` and the future `x[t + 1:n]`, the likelihood is the sum over
the hidden state `«y.bvar» t` at the cut of the forward probability
`ℙ(x[:t + 1] = «x.bvar»[:t + 1] ∧ y t = «y.bvar» t)` times the backward probability
`ℙ(x[t + 1:n] = «x.bvar»[t + 1:n] | y t = «y.bvar» t)`; in particular it does not depend on the cut.

No positivity assumption is needed: a conditional probability given a null event is `0` (division in `ENNReal`),
and then both sides vanish.  The proof derives the one-step factorizations from the emission and Markov conditional
independences of the HMM (for sets of sample paths), runs the forward recursion once from the observed prefix and
once from the observed future, and obtains the forward-backward identity
`ℙ(x[:n] = «x.bvar»[:n] ∧ y t = «y.bvar» t) = α t «y.bvar» t * β t «y.bvar» t` along the way.
-/
@[main]
private lemma main
  {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  [Fintype Y]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {«x.bvar» : ℕ → X}
  {n : ℕ}
-- given
  (h : IsDiscreteHMM π x y)
  (t : Fin n) :
-- imply
  ∑ «y.bvar» t, ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ (y t) = «y.bvar» t) *
      ℙ[π](x[t + 1:n] = «x.bvar»[t + 1:n] | (y t) = «y.bvar» t) = ℙ[π](x[:n] = «x.bvar»[:n]) := by
-- proof
  obtain ⟨t, ht⟩ := t
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ⟨hx, hy, hX, hY, h_emit, h_markov⟩ := h
  have : Nonempty X := ⟨«x.bvar» 0⟩
  obtain ⟨ω₀, -⟩ := nonempty_of_measure_ne_zero (μ := π) (s := Set.univ) (by simp)
  have : Nonempty Y := ⟨y 0 ω₀⟩
  have hpair : ∀ m n : ℕ, ReferenceMeasure.measure (α := (Fin m → X) × (Fin n → Y)) = Measure.count := fun m n => by
    change (Measure.count : Measure (Fin m → X)).prod Measure.count = Measure.count
    rw [← Measure.Count.eq.ProdCountS]
  have hJ : ∀ a b : ℕ, Measurable (x[:(a : ℤ)], y[:(b : ℤ)]) := fun a b =>
    (measurable_pi_lambda _ fun i => hx _).prodMk (measurable_pi_lambda _ fun i => hy _)
  -- events defined by a predicate on the sample paths
  obtain ⟨Ev, hEv⟩ : ∃ Ev : ((ℕ → X) → (ℕ → Y) → Prop) → Set Ω,
      ∀ p, Ev p = {ω | p (fun i => x i ω) (fun i => y i ω)} := ⟨fun p => {ω | p (fun i => x i ω) (fun i => y i ω)}, fun _ => rfl⟩
  obtain ⟨Dep, hDep⟩ : ∃ Dep : ((ℕ → X) → (ℕ → Y) → Prop) → ℕ → ℕ → Prop,
      ∀ p a b, Dep p a b ↔ ∀ f f' g g', (∀ i < a, f i = f' i) → (∀ i < b, g i = g' i) → (p f g ↔ p f' g') :=
    ⟨fun p a b => ∀ f f' g g', (∀ i < a, f i = f' i) → (∀ i < b, g i = g' i) → (p f g ↔ p f' g'), fun _ _ _ => Iff.rfl⟩
  have hrep : ∀ (p : (ℕ → X) → (ℕ → Y) → Prop) (a b : ℕ), Dep p a b → ∃ S, Ev p = (x[:(a : ℤ)], y[:(b : ℤ)]) ⁻¹' S := by
    intro p a b hp
    rw [hDep] at hp
    refine ⟨{v | p (fun i => if h : i < a then v.1 ⟨i, h⟩ else «x.bvar» 0) (fun i => if h : i < b then v.2 ⟨i, h⟩ else y 0 ω₀)}, ?_⟩
    ext ω
    rw [hEv]
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    refine hp _ _ _ _ (fun i hi => ?_) (fun i hi => ?_)
    · simp [hi, JointRandomSymbol]; rfl
    · simp [hi, JointRandomSymbol]; rfl
  have hmeas : ∀ (p : (ℕ → X) → (ℕ → Y) → Prop) (a b : ℕ), Dep p a b → MeasurableSet (Ev p) := by
    intro p a b hp
    obtain ⟨S, hS⟩ := hrep p a b hp
    rw [hS]
    exact hJ a b S.to_countable.measurableSet
  have hdec : ∀ {T : Type (max u_2 u_3)} [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] (K : Ω → T),
      Measurable K → ∀ (E : Set Ω), MeasurableSet E → ∀ S : Set T,
      π (E ∩ K ⁻¹' S) = ∑' v : S, π (E ∩ K ⁻¹' {(v : T)}) := by
    intro T _ _ _ K hK E hE S
    have e : E ∩ K ⁻¹' S = ⋃ v ∈ S, E ∩ K ⁻¹' {v} := by
      ext ω
      simp
    rw [e, measure_biUnion S.to_countable]
    · intro v _ w _ hvw
      refine Set.disjoint_left.2 fun ω hv hw => hvw ?_
      have h1 : K ω = v := hv.2
      have h2 : K ω = w := hw.2
      rw [← h1, ← h2]
    · intro v _
      exact hE.inter (hK (measurableSet_singleton v))
  have hemit : ∀ (s : ℕ) (p : (ℕ → X) → (ℕ → Y) → Prop), Dep p (s + 1) (s + 1) → ∀ (u : X) (w : Y),
      π (x (s + 1) ⁻¹' {u} ∩ Ev p ∩ y (s + 1) ⁻¹' {w}) * π (y (s + 1) ⁻¹' {w}) =
        π (x (s + 1) ⁻¹' {u} ∩ y (s + 1) ⁻¹' {w}) * π (Ev p ∩ y (s + 1) ⁻¹' {w}) := by
    intro s p hp u w
    obtain ⟨S, hS⟩ := hrep p _ _ hp
    have hpt := fun v => Random.MulMeasure.eq.MulMeasure.of.CondIndep (hx (s + 1)) (hJ (s + 1) (s + 1)) (hy (s + 1)) hX (hpair _ _) hY
      (h_emit s (hy (s + 1))) u v w
    have hm1 : MeasurableSet (x (s + 1) ⁻¹' {u} ∩ y (s + 1) ⁻¹' {w}) :=
      (hx _ (measurableSet_singleton u)).inter (hy _ (measurableSet_singleton w))
    have hm2 : MeasurableSet (y (s + 1) ⁻¹' {w}) := hy _ (measurableSet_singleton w)
    rw [hS, Set.inter_right_comm, Set.inter_comm (_ ⁻¹' S), hdec _ (hJ (s + 1) (s + 1)) _ hm1 S, hdec _ (hJ (s + 1) (s + 1)) _ hm2 S,
      ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun v => ?_
    have := hpt v
    rw [Set.inter_right_comm, Set.inter_comm (y (s + 1) ⁻¹' {w})]
    exact this
  have hmark : ∀ (s : ℕ) (p : (ℕ → X) → (ℕ → Y) → Prop), Dep p (s + 1) s → ∀ (c b : Y),
      π (y (s + 1) ⁻¹' {c} ∩ Ev p ∩ y s ⁻¹' {b}) * π (y s ⁻¹' {b}) =
        π (y (s + 1) ⁻¹' {c} ∩ y s ⁻¹' {b}) * π (Ev p ∩ y s ⁻¹' {b}) := by
    intro s p hp c b
    obtain ⟨S, hS⟩ := hrep p _ _ hp
    have hpt := fun v => Random.MulMeasure.eq.MulMeasure.of.CondIndep (hy (s + 1)) (hJ (s + 1) s) (hy s) hY (hpair _ _) hY
      (h_markov s (hy s)) c v b
    have hm1 : MeasurableSet (y (s + 1) ⁻¹' {c} ∩ y s ⁻¹' {b}) :=
      (hy _ (measurableSet_singleton c)).inter (hy _ (measurableSet_singleton b))
    have hm2 : MeasurableSet (y s ⁻¹' {b}) := hy _ (measurableSet_singleton b)
    rw [hS, Set.inter_right_comm, Set.inter_comm (_ ⁻¹' S), hdec _ (hJ (s + 1) s) _ hm1 S, hdec _ (hJ (s + 1) s) _ hm2 S,
      ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun v => ?_
    have := hpt v
    rw [Set.inter_right_comm, Set.inter_comm (y s ⁻¹' {b})]
    exact this
  have hDepMono : ∀ (p : (ℕ → X) → (ℕ → Y) → Prop) (a b a' b' : ℕ), Dep p a b → a ≤ a' → b ≤ b' → Dep p a' b' := by
    intro p a b a' b' hp ha hb
    rw [hDep] at hp ⊢
    exact fun f f' g g' hf hg => hp f f' g g' (fun i hi => hf i (by omega)) (fun i hi => hg i (by omega))
  have hstep : ∀ (s : ℕ) (Q : (ℕ → X) → (ℕ → Y) → Prop), Dep Q (s + 1) (s + 1) → ∀ (b c : Y),
      π (Ev Q ∩ y s ⁻¹' {b} ∩ y (s + 1) ⁻¹' {c} ∩ x (s + 1) ⁻¹' {«x.bvar» (s + 1)}) =
        π (Ev Q ∩ y s ⁻¹' {b}) * (π (y (s + 1) ⁻¹' {c} ∩ y s ⁻¹' {b}) / π (y s ⁻¹' {b}) *
          (π (x (s + 1) ⁻¹' {«x.bvar» (s + 1)} ∩ y (s + 1) ⁻¹' {c}) / π (y (s + 1) ⁻¹' {c}))) := by
    intro s Q hQ b c
    have hQ' := (hDep _ _ _).1 hQ
    have e1 : Ev (fun f g => Q f g ∧ g s = b) = Ev Q ∩ y s ⁻¹' {b} := by
      ext ω
      simp [hEv]
    have hd1 : Dep (fun f g => Q f g ∧ g s = b) (s + 1) (s + 1) := by
      rw [hDep]
      intro f f' g g' hf hg
      rw [hQ' f f' g g' hf hg, hg s (by omega)]
    have e2 : Ev (fun f g => Q f (Function.update g s b)) ∩ y s ⁻¹' {b} = Ev Q ∩ y s ⁻¹' {b} := by
      ext ω
      simp only [hEv, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rwa [← h2, Function.update_eq_self] at h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rwa [← h2, Function.update_eq_self]
    have hd2 : Dep (fun f g => Q f (Function.update g s b)) (s + 1) s := by
      rw [hDep]
      intro f f' g g' hf hg
      refine hQ' f f' _ _ hf (fun i hi => ?_)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · rw [Function.update_of_ne h.ne, Function.update_of_ne h.ne]
        exact hg i h
      · simp
    have h₁ := hemit s _ hd1 («x.bvar» (s + 1)) c
    have h₂ := hmark s _ hd2 c b
    rw [e1] at h₁
    rw [Set.inter_assoc, e2] at h₂
    exact Random.Measure.eq.Mul_MulDivS.of.Subset (C := Ev Q ∩ y s ⁻¹' {b}) (E := x (s + 1) ⁻¹' {«x.bvar» (s + 1)})
      (F := y (s + 1) ⁻¹' {c}) (G := y s ⁻¹' {b}) Set.inter_subset_right h₁ h₂
  have hEvy : ∀ (Q : (ℕ → X) → (ℕ → Y) → Prop) (s : ℕ) (b : Y), Ev (fun f g => Q f g ∧ g s = b) = Ev Q ∩ y s ⁻¹' {b} := by
    intro Q s b
    ext ω
    simp [hEv]
  have hpart : ∀ (s : ℕ) (E : Set Ω), (∀ b, MeasurableSet (E ∩ y s ⁻¹' {b})) → π E = ∑ b, π (E ∩ y s ⁻¹' {b}) := by
    intro s E hE
    have e : E = ⋃ b, E ∩ y s ⁻¹' {b} := by
      ext ω
      simp
    conv_lhs => rw [e]
    rw [measure_iUnion, tsum_fintype]
    · intro b b' hbb'
      refine Set.disjoint_left.2 fun ω hb hb' => hbb' ?_
      have h1 : y s ω = b := hb.2
      have h2 : y s ω = b' := hb'.2
      rw [← h1, ← h2]
    · exact hE
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → Y → Y → ENNReal, ∀ s b c, ψ s b c =
      π (y (s + 1) ⁻¹' {c} ∩ y s ⁻¹' {b}) / π (y s ⁻¹' {b}) *
        (π (x (s + 1) ⁻¹' {«x.bvar» (s + 1)} ∩ y (s + 1) ⁻¹' {c}) / π (y (s + 1) ⁻¹' {c})) := ⟨_, fun _ _ _ => rfl⟩
  have hrec : ∀ (s : ℕ) (Q Q' : (ℕ → X) → (ℕ → Y) → Prop), Dep Q (s + 1) (s + 1) →
      (∀ f g, Q' f g ↔ Q f g ∧ f (s + 1) = «x.bvar» (s + 1)) → ∀ c : Y,
      π (Ev Q' ∩ y (s + 1) ⁻¹' {c}) = ∑ b, π (Ev Q ∩ y s ⁻¹' {b}) * ψ s b c := by
    intro s Q Q' hQ hQ' c
    have hm : ∀ b, MeasurableSet (Ev Q ∩ y s ⁻¹' {b} ∩ y (s + 1) ⁻¹' {c} ∩ x (s + 1) ⁻¹' {«x.bvar» (s + 1)}) := fun b =>
      (((hmeas Q _ _ hQ).inter (hy _ (measurableSet_singleton b))).inter (hy _ (measurableSet_singleton c))).inter
        (hx _ (measurableSet_singleton _))
    have e : ∀ b, (Ev Q' ∩ y (s + 1) ⁻¹' {c}) ∩ y s ⁻¹' {b} =
        Ev Q ∩ y s ⁻¹' {b} ∩ y (s + 1) ⁻¹' {c} ∩ x (s + 1) ⁻¹' {«x.bvar» (s + 1)} := by
      intro b
      ext ω
      simp only [hEv, hQ', Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      tauto
    rw [hpart s _ (fun b => by rw [e]; exact hm b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [e, hstep s Q hQ b c, hψ]
  have hinv : ∀ (t : ℕ) (a : Y) (k : ℕ) (b : Y),
      π (Ev (fun f g => (∀ i ≤ t + k, f i = «x.bvar» i) ∧ g t = a) ∩ y (t + k) ⁻¹' {b}) * π (y t ⁻¹' {a}) =
        π (Ev (fun f g => (∀ i ≤ t, f i = «x.bvar» i) ∧ g t = a)) *
          π (Ev (fun f g => (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ∧ g t = a) ∩ y (t + k) ⁻¹' {b}) := by
    intro t a k
    induction k with
    | zero =>
      intro b
      by_cases hb : b = a
      · subst hb
        have e1 : Ev (fun f g => (∀ i ≤ t + 0, f i = «x.bvar» i) ∧ g t = b) ∩ y (t + 0) ⁻¹' {b} =
            Ev (fun f g => (∀ i ≤ t, f i = «x.bvar» i) ∧ g t = b) := by
          ext ω
          simp [hEv]
        have e2 : Ev (fun f g => (∀ i, t < i → i ≤ t + 0 → f i = «x.bvar» i) ∧ g t = b) ∩ y (t + 0) ⁻¹' {b} =
            y t ⁻¹' {b} := by
          ext ω
          simp only [hEv, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, add_zero]
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨⟨fun i h1 h2 => absurd h1 (by omega), h⟩, h⟩
        rw [e1, e2]
      · have e1 : Ev (fun f g => (∀ i ≤ t + 0, f i = «x.bvar» i) ∧ g t = a) ∩ y (t + 0) ⁻¹' {b} = ∅ := by
          ext ω
          simp only [hEv, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, add_zero,
            Set.mem_empty_iff_false, iff_false]
          exact fun h => hb (h.2.symm.trans h.1.2)
        have e2 : Ev (fun f g => (∀ i, t < i → i ≤ t + 0 → f i = «x.bvar» i) ∧ g t = a) ∩ y (t + 0) ⁻¹' {b} = ∅ := by
          ext ω
          simp only [hEv, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, add_zero,
            Set.mem_empty_iff_false, iff_false]
          exact fun h => hb (h.2.symm.trans h.1.2)
        rw [e1, e2]
        simp
    | succ k ih =>
      intro c
      have hdA : Dep (fun f g => (∀ i ≤ t + k, f i = «x.bvar» i) ∧ g t = a) (t + k + 1) (t + k + 1) := by
        rw [hDep]
        intro f f' g g' hf hg
        have e : (∀ i ≤ t + k, f i = «x.bvar» i) ↔ (∀ i ≤ t + k, f' i = «x.bvar» i) :=
          forall₂_congr fun i hi => by rw [hf i (by omega)]
        rw [e, hg t (by omega)]
      have hdN : Dep (fun f g => (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ∧ g t = a) (t + k + 1) (t + k + 1) := by
        rw [hDep]
        intro f f' g g' hf hg
        have e : (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ↔ (∀ i, t < i → i ≤ t + k → f' i = «x.bvar» i) :=
          forall_congr' fun i => forall_congr' fun _ => forall_congr' fun hi => by rw [hf i (by omega)]
        rw [e, hg t (by omega)]
      have rA := hrec (t + k) _ (fun f g => (∀ i ≤ t + k + 1, f i = «x.bvar» i) ∧ g t = a) hdA
        (fun f g => by
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨⟨fun i hi => h1 i (by omega), h2⟩, h1 _ (by omega)⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩
            refine ⟨fun i hi => ?_, h2⟩
            by_cases hi' : i ≤ t + k
            · exact h1 i hi'
            · obtain rfl : i = t + k + 1 := by omega
              exact h3) c
      have rN := hrec (t + k) _ (fun f g => (∀ i, t < i → i ≤ t + k + 1 → f i = «x.bvar» i) ∧ g t = a) hdN
        (fun f g => by
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨⟨fun i h3 hi => h1 i h3 (by omega), h2⟩, h1 _ (by omega) (by omega)⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩
            refine ⟨fun i h4 hi => ?_, h2⟩
            by_cases hi' : i ≤ t + k
            · exact h1 i h4 hi'
            · obtain rfl : i = t + k + 1 := by omega
              exact h3) c
      rw [show t + (k + 1) = t + k + 1 from rfl, rA, rN, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_right_comm, ih b, mul_assoc]
  have hpair' : ∀ N : ℕ, ReferenceMeasure.measure (α := (Fin N → X) × Y) = Measure.count := fun N => by
    show (Measure.count : Measure (Fin N → X)).prod (ReferenceMeasure.measure (α := Y)) = Measure.count
    rw [hY, ← Measure.Count.eq.ProdCountS]
  have hP1 : ∀ (n j : ℕ) (a : Y), ℙ[π](x[:n + 1] = «x.bvar»[:n + 1] ∧ (y j) = a) =
      π (Ev (fun f g => ∀ i ≤ n, f i = «x.bvar» i) ∩ y j ⁻¹' {a}) := by
    intro n j a
    rw [Random.Prob.eq.Measure.of.Eq_Count (hpair' _)]
    congr 1
    ext ω
    simp only [hEv, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, JointRandomSymbol,
      Prod.mk.injEq, funext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i hi => h1 ⟨i, by simpa using Nat.lt_succ_of_le hi⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => h1 i (by have := i.2; simp at this; omega), h2⟩
  have hP3 : ∀ n : ℕ, ℙ[π](x[:n + 1] = «x.bvar»[:n + 1]) = π (Ev (fun f g => ∀ i ≤ n, f i = «x.bvar» i)) := by
    intro n
    rw [Random.Prob.eq.Measure.of.Eq_Count rfl]
    congr 1
    ext ω
    simp only [hEv, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
    constructor
    · intro h1 i hi
      exact h1 ⟨i, by simpa using Nat.lt_succ_of_le hi⟩
    · intro h1 i
      exact h1 i (by have := i.2; simp at this; omega)
  have hP2 : ∀ (t m : ℕ) (a : Y), ℙ[π](x[t + 1:m + 1] = «x.bvar»[t + 1:m + 1] | (y t) = a) =
      π (Ev (fun f g => ∀ i, t < i → i ≤ m → f i = «x.bvar» i) ∩ y t ⁻¹' {a}) / π (y t ⁻¹' {a}) := by
    intro t m a
    rw [Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count rfl hY]
    congr 2
    ext ω
    simp only [hEv, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, funext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi1 hi2 => ?_, h2⟩
      have := h1 ⟨i - (t + 1), by show i - (t + 1) < m + 1 - (t + 1); omega⟩
      have e : i - (t + 1) + (t + 1) = i := by omega
      change x (i - (t + 1) + (t + 1)) ω = «x.bvar» (i - (t + 1) + (t + 1)) at this
      rwa [e] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => h1 (j.val + (t + 1)) (by omega) (by have := j.2; change j.val < m + 1 - (t + 1) at this; omega), h2⟩
  have hPcond : ∀ (i j : ℕ) (u : X) (b : Y), ℙ[π]((x i) = u | (y j) = b) =
      π (x i ⁻¹' {u} ∩ y j ⁻¹' {b}) / π (y j ⁻¹' {b}) :=
    fun i j u b => Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count hX hY u b
  have hPcondy : ∀ (i j : ℕ) (c b : Y), ℙ[π]((y i) = c | (y j) = b) =
      π (y i ⁻¹' {c} ∩ y j ⁻¹' {b}) / π (y j ⁻¹' {b}) :=
    fun i j c b => Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count hY hY c b
  have hPy : ∀ (j : ℕ) (b : Y), ℙ[π]((y j) = b) = π (y j ⁻¹' {b}) :=
    fun j b => Random.Prob.eq.Measure.of.Eq_Count hY b
  have hdA : ∀ (t : ℕ) (a : Y) (k : ℕ),
      Dep (fun f g => (∀ i ≤ t + k, f i = «x.bvar» i) ∧ g t = a) (t + k + 1) (t + k + 1) := by
    intro t a k
    rw [hDep]
    intro f f' g g' hf hg
    have e : (∀ i ≤ t + k, f i = «x.bvar» i) ↔ (∀ i ≤ t + k, f' i = «x.bvar» i) :=
      forall₂_congr fun i hi => by rw [hf i (by omega)]
    rw [e, hg t (by omega)]
  have hdN : ∀ (t : ℕ) (a : Y) (k : ℕ),
      Dep (fun f g => (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ∧ g t = a) (t + k + 1) (t + k + 1) := by
    intro t a k
    rw [hDep]
    intro f f' g g' hf hg
    have e : (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ↔ (∀ i, t < i → i ≤ t + k → f' i = «x.bvar» i) :=
      forall_congr' fun i => forall_congr' fun _ => forall_congr' fun hi => by rw [hf i (by omega)]
    rw [e, hg t (by omega)]
  have hdM : ∀ n : ℕ, Dep (fun f (_ : ℕ → Y) => ∀ i ≤ n, f i = «x.bvar» i) (n + 1) (n + 1) := by
    intro n
    rw [hDep]
    intro f f' g g' hf hg
    exact forall₂_congr fun i hi => by rw [hf i (by omega)]
  have hsumA : ∀ (t : ℕ) (a : Y) (k : ℕ), π (Ev (fun f g => (∀ i ≤ t + k, f i = «x.bvar» i) ∧ g t = a)) =
      ∑ b, π (Ev (fun f g => (∀ i ≤ t + k, f i = «x.bvar» i) ∧ g t = a) ∩ y (t + k) ⁻¹' {b}) := fun t a k =>
    hpart (t + k) _ (fun b => (hmeas _ _ _ (hdA t a k)).inter (hy _ (measurableSet_singleton b)))
  have hsumN : ∀ (t : ℕ) (a : Y) (k : ℕ), π (Ev (fun f g => (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ∧ g t = a)) =
      ∑ b, π (Ev (fun f g => (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ∧ g t = a) ∩ y (t + k) ⁻¹' {b}) := fun t a k =>
    hpart (t + k) _ (fun b => (hmeas _ _ _ (hdN t a k)).inter (hy _ (measurableSet_singleton b)))
  have hfwd : ∀ (t : ℕ) (a : Y), ℙ[π](x[:t + 1 + 1] = «x.bvar»[:t + 1 + 1] ∧ (y (t + 1)) = a) =
      ∑ «y.bvar», ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ (y t) = «y.bvar») * ℙ[π]((y (t + 1)) = a | (y t) = «y.bvar») *
        ℙ[π]((x (t + 1)) = «x.bvar» (t + 1) | (y (t + 1)) = a) := by
    intro t a
    refine (hP1 (t + 1) (t + 1) a).trans ?_
    rw [hrec t (fun f (_ : ℕ → Y) => ∀ i ≤ t, f i = «x.bvar» i) _ (hDepMono _ _ _ _ _ (hdM t) le_rfl le_rfl)
      (fun f g => by
        constructor
        · intro h1
          exact ⟨fun i hi => h1 i (by omega), h1 _ le_rfl⟩
        · rintro ⟨h1, h2⟩ i hi
          by_cases hi' : i ≤ t
          · exact h1 i hi'
          · obtain rfl : i = t + 1 := by omega
            exact h2)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hP1, hPcondy, hPcond, hψ, mul_assoc]
  have hfb : ∀ (t : ℕ), t ≤ m → ∀ a, ℙ[π](x[:m + 1] = «x.bvar»[:m + 1] ∧ (y t) = a) =
      ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ (y t) = a) *
        ℙ[π](x[t + 1:m + 1] = «x.bvar»[t + 1:m + 1] | (y t) = a) := by
    intro t ht a
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [hP1, hP1, hP2]
    have e1 := hEvy (fun f (_ : ℕ → Y) => ∀ i ≤ t + k, f i = «x.bvar» i) t a
    have e2 := hEvy (fun f (_ : ℕ → Y) => ∀ i ≤ t, f i = «x.bvar» i) t a
    have e3 := hEvy (fun f (_ : ℕ → Y) => ∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) t a
    rw [← e1, ← e2, ← e3]
    have hs : π (Ev (fun f g => (∀ i ≤ t + k, f i = «x.bvar» i) ∧ g t = a)) * π (y t ⁻¹' {a}) =
        π (Ev (fun f g => (∀ i ≤ t, f i = «x.bvar» i) ∧ g t = a)) *
          π (Ev (fun f g => (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ∧ g t = a)) := by
      rw [hsumA, hsumN, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => hinv t a k b
    by_cases hP : π (y t ⁻¹' {a}) = 0
    · have h1 : π (Ev (fun f g => (∀ i ≤ t + k, f i = «x.bvar» i) ∧ g t = a)) = 0 := by
        refine measure_mono_null (fun ω hω => ?_) hP
        rw [hEv] at hω
        exact hω.2
      have h2 : π (Ev (fun f g => (∀ i, t < i → i ≤ t + k → f i = «x.bvar» i) ∧ g t = a)) = 0 := by
        refine measure_mono_null (fun ω hω => ?_) hP
        rw [hEv] at hω
        exact hω.2
      rw [h1, h2, hP]
      simp
    · rw [← mul_div_assoc]
      exact (ENNReal.eq_div_iff hP (measure_ne_top _ _)).2 (by rw [mul_comm]; exact hs)
  replace ht : t ≤ m := by omega
  refine (Finset.sum_congr rfl fun a _ => (hfb t ht a).symm).trans ?_
  push_cast
  rw [hP3]
  simp only [hP1]
  rw [hpart t _ (fun b => (hmeas _ _ _ (hdM m)).inter (hy _ (measurableSet_singleton b)))]


-- created on 2026-10-03
-- updated on 2026-10-05
