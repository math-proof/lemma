import Mathlib.Topology.Instances.EReal.Lemmas
import Lemma.Finset.Limsup.eq.NegLiminf.of.All_GtToReal_0.All_Nonempty.All_EqSum
open EReal Filter Finset MeasureTheory Real


private lemma limsup_le_neg_iInf [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {s : ℕ → Finset (α → ℕ)} {μ : PMF α} {A : Set (α → ℝ)} (hs : ∀ n, 0 < n → ∀ c ∈ s n, ∑ a, c a = n) (hne : ∀ n, 0 < n → (s n).Nonempty) (hμ : ∀ n, 0 < n → ∀ c ∈ s n, ∀ a, 0 < c a → 0 < (μ a).toReal) (hA : ∀ n, 0 < n → ∀ c ∈ s n, (fun a => (c a : ℝ) / n) ∈ A) :
  limsup (fun n : ℕ => toEReal (((n + 1 : ℕ) : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin (n + 1) => μ.toMeasure) (⋃ c ∈ s (n + 1), (empiricalSet (n + 1) c : Set (Fin (n + 1) → α)))).toReal))) atTop ≤
    - ⨅ ν ∈ A, toEReal (∑ a, ν a * log (ν a / (μ a).toReal)) := by
  rw [Limsup.eq.NegLiminf.of.All_GtToReal_0.All_Nonempty.All_EqSum hs hne hμ, neg_le_neg_iff, liminf_eq]
  refine le_sSup ?_
  filter_upwards with n
  obtain ⟨cMin, hcMin, hmin⟩ := exists_mem_eq_inf' (hne (n + 1) n.succ_pos)
    (fun c => ∑ a, ((c a : ℝ) / (n + 1)) * log (((c a : ℝ) / (n + 1)) / (μ a).toReal))
  rw [hmin]
  exact iInf₂_le (f := fun ν (_ : ν ∈ A) => toEReal (∑ a, ν a * log (ν a / (μ a).toReal)))
    (fun a => (cMin a : ℝ) / (↑n + 1)) (by simpa [Nat.cast_add] using hA (n + 1) n.succ_pos cMin hcMin)

/--
If every empirical type in the family lies in a set `A` of real vectors, the limsup of `(1/n) log`
of its probability is at most the negative infimum of `KL(ν ‖ μ)` over `A`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {s : ℕ → Finset (α → ℕ)} {μ : PMF α} {A : Set (α → ℝ)}
-- given
  (hs : ∀ n, 0 < n → ∀ c ∈ s n, ∑ a, c a = n)
  (hne : ∀ n, 0 < n → (s n).Nonempty)
  (hμ : ∀ n, 0 < n → ∀ c ∈ s n, ∀ a, 0 < c a → 0 < (μ a).toReal)
  (hA : ∀ n, 0 < n → ∀ c ∈ s n, (fun a => (c a : ℝ) / n) ∈ A) :
-- imply
  limsup (fun n : ℕ => toEReal (((n + 1 : ℕ) : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin (n + 1) => μ.toMeasure) (⋃ c ∈ s (n + 1), (empiricalSet (n + 1) c : Set (Fin (n + 1) → α)))).toReal))) atTop ≤
    - ⨅ ν ∈ A, toEReal (∑ a, ν a * log (ν a / (μ a).toReal)) :=
-- proof
  limsup_le_neg_iInf hs hne hμ hA


-- created on 2026-11-02
