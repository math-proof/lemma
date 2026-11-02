import Mathlib.Basic.ENNReal.BigOperators
import Lemma.Fin.Pi_ToMeasure.of.EqSum
import Lemma.Finset.AbsAddMulInvLogInf'.le.DivMulCardAddAddLogDivLog2'1.of.All_Gt_0.Nonempty.All_EqSum.Gt_0
open ENNReal Fin Finset MeasureTheory Real


private lemma disjoint_empiricalSet [Fintype α] [DecidableEq α] (n : ℕ) {c d : α → ℕ} (hne : c ≠ d) :
  Disjoint (empiricalSet n c : Set (Fin n → α)) (empiricalSet n d : Set (Fin n → α)) := by
  rw [Set.disjoint_left]
  intro ω hc hd
  apply hne
  ext a
  simp only [empiricalSet, mem_coe, mem_filter, mem_univ, true_and] at hc hd
  exact (hc a).symm.trans (hd a)

private lemma pairwise_empiricalSet [Fintype α] [DecidableEq α] (n : ℕ) (s : Finset (α → ℕ)) :
  Set.PairwiseDisjoint (s : Set (α → ℕ)) (fun c => (empiricalSet n c : Set (Fin n → α))) := by
  intro c _ d _ hne
  apply disjoint_empiricalSet n hne

private lemma empiricalSet_eq [Fintype α] [DecidableEq α] (n : ℕ) (c : α → ℕ) :
  (empiricalSet n c : Set (Fin n → α)) = {ω | ∀ a, countVec ω a = c a} := by
  ext ω
  simp [empiricalSet]

private lemma measure_union [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ} (s : Finset (α → ℕ)) (hs : ∀ c ∈ s, ∑ a, c a = n) (μ : PMF α) :
  (Measure.pi fun _ : Fin n => μ.toMeasure) (⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α))) =
    ∑ c ∈ s, (Nat.multinomial univ c : ENNReal) * ∏ a, μ a ^ c a := by
  rw [measure_biUnion_finset (pairwise_empiricalSet n s) (fun c _ => (empiricalSet n c).measurableSet)]
  refine sum_congr rfl fun c hc => ?_
  rw [empiricalSet_eq n c]
  apply Pi_ToMeasure.of.EqSum (hs c hc) μ

private lemma mass_ne_top [Fintype α] [DecidableEq α] (μ : PMF α) (c : α → ℕ) :
  (Nat.multinomial univ c : ENNReal) * ∏ a, μ a ^ c a ≠ ⊤ := by
  apply mul_ne_top
  ·
    apply natCast_ne_top
  ·
    apply prod_ne_top
    intro a _
    apply pow_ne_top
    apply μ.apply_ne_top

private lemma toReal_union [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ} (s : Finset (α → ℕ)) (hs : ∀ c ∈ s, ∑ a, c a = n) (μ : PMF α) :
  ((Measure.pi fun _ : Fin n => μ.toMeasure) (⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α)))).toReal =
    ∑ c ∈ s, (Nat.multinomial univ c : ℝ) * ∏ a, (μ a).toReal ^ c a := by
  rw [measure_union s hs μ, toReal_sum (fun c _ => mass_ne_top μ c)]
  refine sum_congr rfl fun c _ => ?_
  simp only [toReal_mul, toReal_natCast, toReal_prod, toReal_pow]

private lemma log_prob [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ} {s : Finset (α → ℕ)} {μ : PMF α} (hn : 0 < n) (hs : ∀ c ∈ s, ∑ a, c a = n) (hne : s.Nonempty) (hμ : ∀ c ∈ s, ∀ a, 0 < c a → 0 < (μ a).toReal) :
  |(n : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin n => μ.toMeasure) (⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α)))).toReal) + s.inf' hne (fun c => ∑ a, ((c a : ℝ) / n) * log (((c a : ℝ) / n) / (μ a).toReal))| ≤
    (Fintype.card α : ℝ) * (log (n + 1) + log n / 2 + 1) / n := by
  rw [toReal_union s hs μ]
  apply AbsAddMulInvLogInf'.le.DivMulCardAddAddLogDivLog2'1.of.All_Gt_0.Nonempty.All_EqSum.Gt_0 hn hs hne hμ

/--
The product measure of a nonempty union of empirical types has logarithmic probability
`-inf KL(c/n ‖ μ)`, up to `|α| (log (n + 1) + log n / 2 + 1) / n`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {n : ℕ} {s : Finset (α → ℕ)} {μ : PMF α}
-- given
  (hn : 0 < n)
  (hs : ∀ c ∈ s, ∑ a, c a = n)
  (hne : s.Nonempty)
  (hμ : ∀ c ∈ s, ∀ a, 0 < c a → 0 < (μ a).toReal) :
-- imply
  |(n : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin n => μ.toMeasure) (⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α)))).toReal) + s.inf' hne (fun c => ∑ a, ((c a : ℝ) / n) * log (((c a : ℝ) / n) / (μ a).toReal))| ≤
    (Fintype.card α : ℝ) * (log (n + 1) + log n / 2 + 1) / n :=
-- proof
  log_prob hn hs hne hμ


-- created on 2026-11-02
