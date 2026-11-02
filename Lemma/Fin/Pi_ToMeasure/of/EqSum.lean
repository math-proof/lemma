import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Initialize.Tactic.Attr.Basic
open Finset MeasureTheory
open scoped ENNReal Nat


/-- Number of coordinates of `ω` equal to `a`. -/
def countVec {α : Type*} [DecidableEq α] {n : ℕ} (ω : Fin n → α) (a : α) : ℕ :=
  ∑ i, if ω i = a then 1 else 0

private lemma countVec_eq_card {α : Type*} [DecidableEq α] {n : ℕ} (ω : Fin n → α) (a : α) :
  countVec ω a = #{i | ω i = a} := by
  simp only [countVec]
  exact Finset.sum_boole (fun i => ω i = a) univ

private lemma countVec_cons {α : Type*} [DecidableEq α] {n : ℕ} (x : α) (p : Fin n → α) (b : α) :
  countVec (Fin.cons x p) b = countVec p b + if x = b then 1 else 0 := by
  simp only [countVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_comm]

/-- Decrement the count of one letter. -/
def predCount {α : Type*} [DecidableEq α] (c : α → ℕ) (a : α) : α → ℕ :=
  Function.update c a (c a - 1)

private lemma sum_predCount {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (a : α) (ha : 0 < c a) (hsum : ∑ i, c i = n + 1) : ∑ i, predCount c a i = n := by
  have hupd : ∑ i, predCount c a i = (c a - 1) + ∑ i ∈ univ \ {a}, c i := by
    simpa [predCount] using Finset.sum_update_of_mem (mem_univ a) c (c a - 1)
  have herase : c a + ∑ i ∈ univ.erase a, c i = ∑ i, c i :=
    Finset.add_sum_erase univ c (mem_univ a)
  have hdiff : univ.erase a = univ \ {a} := by ext; simp
  rw [hdiff] at herase
  omega

private lemma prod_factorial_predCount {α : Type*} [Fintype α] [DecidableEq α] (c : α → ℕ) (a : α) (ha : 0 < c a) : ∏ i, (c i)! = c a * ∏ i, (predCount c a i)! := by
  have hfac : (c a)! = c a * (c a - 1)! := by
    rw [show c a = (c a - 1) + 1 by omega, Nat.factorial_succ]
    simp
  have hfun :
    (fun i => (predCount c a i)!) = Function.update (fun i => (c i)!) a ((c a - 1)!) := by
    funext i
    if hi : i = a then
      simp [predCount, hi]
    else
      simp [predCount, Function.update_of_ne hi]
  calc
    _ = (c a)! * ∏ i ∈ univ.erase a, (c i)! := by
      rw [← Finset.mul_prod_erase univ (fun i => (c i)!) (mem_univ a)]
    _ = c a * ((c a - 1)! * ∏ i ∈ univ.erase a, (c i)!) := by
      rw [hfac]
      ring
    _ = c a * ∏ i, (predCount c a i)! := by
      rw [hfun, Finset.prod_update_of_mem (mem_univ a)]
      have hdiff : univ.erase a = univ \ {a} := by ext; simp
      rw [hdiff]

private lemma mul_multinomial_predCount {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (a : α) (ha : 0 < c a) (hsum : ∑ i, c i = n + 1) : c a * Nat.multinomial univ c = (n + 1) * Nat.multinomial univ (predCount c a) := by
  have hsum' : ∑ i, predCount c a i = n := sum_predCount c a ha hsum
  have hspec := Nat.multinomial_spec univ c
  have hspec' := Nat.multinomial_spec univ (predCount c a)
  rw [hsum] at hspec
  rw [hsum'] at hspec'
  have hprod := prod_factorial_predCount c a ha
  apply Nat.mul_left_cancel (Nat.prod_factorial_pos (s := univ) (f := predCount c a))
  calc
    _ = (c a * ∏ i, (predCount c a i)!) * Nat.multinomial univ c := by
      ring
    _ = (∏ i, (c i)!) * Nat.multinomial univ c := by
      rw [← hprod]
    _ = (n + 1)! := hspec
    _ = (n + 1) * n ! := Nat.factorial_succ n
    _ = (n + 1) * ((∏ i, (predCount c a i)!) * Nat.multinomial univ (predCount c a)) := by
      rw [← hspec']
    _ = (∏ i, (predCount c a i)!) * ((n + 1) * Nat.multinomial univ (predCount c a)) := by
      ring

private lemma sum_multinomial_predCount {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (hsum : ∑ a, c a = n + 1) : ∑ a ∈ univ.filter (fun a => 0 < c a), Nat.multinomial univ (predCount c a) = Nat.multinomial univ c := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
  rw [Finset.mul_sum]
  have hterm : ∀ a ∈ univ.filter (fun a => 0 < c a),
    (n + 1) * Nat.multinomial univ (predCount c a) = c a * Nat.multinomial univ c := by
    intro a ha
    exact (mul_multinomial_predCount c a (mem_filter.mp ha).2 hsum).symm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, Finset.sum_filter]
  have hzero : ∑ a, (if 0 < c a then c a else 0) = ∑ a, c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · omega
  rw [hzero, hsum]

/-- Samples whose empirical counts are exactly `c`. -/
def empiricalSet {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) (c : α → ℕ) :
  Finset (Fin n → α) :=
  {ω | ∀ a, countVec ω a = c a}

private lemma card_empiricalSet {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (hsum : ∑ a, c a = n) : #(empiricalSet n c) = Nat.multinomial univ c := by
  induction n generalizing c with
  | zero =>
    have hc : ∀ a, c a = 0 := by
      intro a
      have hle : c a ≤ ∑ i, c i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)
      omega
    have hempty : ∀ (ω : Fin 0 → α) (a : α), countVec ω a = 0 := by
      intro ω a
      simp [countVec]
    have hset : empiricalSet 0 c = univ := by
      ext ω
      simp [empiricalSet, hempty, hc]
    rw [hset, card_univ]
    have hcard : Fintype.card (Fin 0 → α) = 1 := by simp
    rw [hcard, Nat.multinomial]
    simp [hc, Nat.factorial_zero]
  | succ n ih =>
    let support := univ.filter (fun a => 0 < c a)
    let source := support.sigma (fun a => empiricalSet n (predCount c a))
    have hcard_source : #source = ∑ a ∈ support, Nat.multinomial univ (predCount c a) := by
      rw [Finset.card_sigma]
      refine Finset.sum_congr rfl fun a ha => ?_
      exact ih (predCount c a) (sum_predCount c a (mem_filter.mp ha).2 hsum)
    have hbij : #source = #(empiricalSet (n + 1) c) := by
      apply Finset.card_bij (s := source) (t := empiricalSet (n + 1) c)
        (i := fun p _ => Fin.cons p.1 p.2)
      ·
        intro p hp
        simp only [source, mem_sigma, support, mem_filter, mem_univ, true_and, empiricalSet] at hp ⊢
        obtain ⟨ha, hω⟩ := hp
        intro b
        have ha0 : 0 < c p.1 := ha
        have htail : countVec p.2 b = predCount c p.1 b := hω b
        rw [countVec_cons, htail]
        if hb : p.1 = b then
          have hb0 : 0 < c b := hb ▸ ha0
          rw [predCount, hb, Function.update_self, ite_eq_left rfl]
          change (c b - 1) + 1 = c b
          omega
        else
          rw [predCount, Function.update_of_ne (Ne.symm hb), ite_eq_right hb]
          simp
      ·
        intro p₁ _ p₂ _ heq
        cases p₁ with
        | mk a₁ ω₁ =>
          cases p₂ with
          | mk a₂ ω₂ =>
            obtain ⟨rfl, rfl⟩ := Fin.cons_inj.mp heq
            rfl
      ·
        intro ω hω
        refine ⟨⟨ω 0, Fin.tail ω⟩, ?_, ?_⟩
        ·
          simp only [source, mem_sigma, support, mem_filter, mem_univ, true_and]
          have hcount : ∀ a, countVec ω a = c a := by simpa [empiricalSet] using hω
          have hpos : 0 < c (ω 0) := by
            have hone : 0 ∈ univ.filter (fun i : Fin (n + 1) => ω i = ω 0) := by simp
            have hcard : 0 < #{i | ω i = ω 0} := Finset.card_pos.mpr ⟨0, hone⟩
            rwa [← hcount, countVec_eq_card]
          refine ⟨hpos, ?_⟩
          simp only [empiricalSet, mem_filter, mem_univ, true_and]
          intro b
          have hcons : countVec (Fin.cons (ω 0) (Fin.tail ω)) b = c b := by
            rw [Fin.cons_self_tail]
            exact hcount b
          rw [countVec_cons] at hcons
          if hb : ω 0 = b then
            have hb0 : 0 < c b := hb ▸ hpos
            simp [predCount, hb] at hcons ⊢
            omega
          else
            rw [predCount, Function.update_of_ne (Ne.symm hb)]
            simp only [hb, ite_false, add_zero] at hcons
            exact hcons
        · simp [Fin.cons_self_tail]
    rw [← hbij, hcard_source]
    simpa [support] using sum_multinomial_predCount c hsum

private lemma pi_singleton_count {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : PMF α) {n : ℕ} (ω : Fin n → α) : (Measure.pi fun _ : Fin n => μ.toMeasure) {ω} = ∏ a, (μ a : ℝ≥0∞) ^ countVec ω a := by
  rw [Measure.pi_singleton]
  have hsing : ∀ i, μ.toMeasure {ω i} = (μ (ω i) : ℝ≥0∞) := fun i =>
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  simp_rw [hsing]
  rw [← Finset.prod_fiberwise' (univ : Finset (Fin n)) ω (fun a => (μ a : ℝ≥0∞))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_const, countVec_eq_card]

private lemma measure_empiricalSet {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : PMF α) {n : ℕ} (c : α → ℕ) : (Measure.pi fun _ : Fin n => μ.toMeasure) (empiricalSet n c : Set (Fin n → α)) = #(empiricalSet n c) * ∏ a, (μ a : ℝ≥0∞) ^ c a := by
  let s := empiricalSet n c
  have hs : (s : Set (Fin n → α)) = ⋃ ω ∈ s, {ω} := by
    ext ω
    simp
  rw [hs]
  have hdisj : Set.PairwiseDisjoint (s : Set (Fin n → α)) (fun ω => ({ω} : Set _)) := by
    intro ω _ ω' _ hne
    exact Set.disjoint_singleton.2 hne
  rw [measure_biUnion_finset hdisj (fun ω _ => measurableSet_singleton ω)]
  have hmass : ∀ ω ∈ s, (Measure.pi fun _ : Fin n => μ.toMeasure) {ω} =
    ∏ a, (μ a : ℝ≥0∞) ^ c a := by
    intro ω hω
    rw [pi_singleton_count]
    have hω' : ∀ a, countVec ω a = c a := by simpa [s, empiricalSet] using hω
    simp [hω']
  rw [Finset.sum_congr rfl hmass, Finset.sum_const, nsmul_eq_mul]

/--
An i.i.d. sample of length `n` from a finite alphabet hits one empirical count `c`
with the multinomial probability. This is the finite-alphabet input to Sanov's theorem:
the law of the empirical measure on a single type is `n! / ∏ (c a)! · ∏ μ(a)^{c a}`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {n : ℕ} {c : α → ℕ}
-- given
  (h : ∑ a, c a = n)
  (μ : PMF α) :
-- imply
  (Measure.pi fun _ : Fin n => μ.toMeasure)
    {ω : Fin n → α | ∀ a, countVec ω a = c a} =
    (Nat.multinomial univ c : ℝ≥0∞) * ∏ a, (μ a : ℝ≥0∞) ^ c a := by
-- proof
  have hset : {ω : Fin n → α | ∀ a, countVec ω a = c a} = empiricalSet n c := by
    ext ω
    simp [empiricalSet]
  rw [hset, measure_empiricalSet, card_empiricalSet c h]


-- created on 2026-11-01
