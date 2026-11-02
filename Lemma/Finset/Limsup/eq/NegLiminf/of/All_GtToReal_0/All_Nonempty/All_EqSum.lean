import Mathlib.Topology.Instances.EReal.Lemmas
import Lemma.Finset.Tendsto.of.All_GtToReal_0.All_Nonempty.All_EqSum
open EReal Filter Finset MeasureTheory Real


private lemma limsup_eq_neg_liminf [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {s : ℕ → Finset (α → ℕ)} {μ : PMF α} (hs : ∀ n, 0 < n → ∀ c ∈ s n, ∑ a, c a = n) (hne : ∀ n, 0 < n → (s n).Nonempty) (hμ : ∀ n, 0 < n → ∀ c ∈ s n, ∀ a, 0 < c a → 0 < (μ a).toReal) :
  limsup (fun n : ℕ => toEReal (((n + 1 : ℕ) : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin (n + 1) => μ.toMeasure) (⋃ c ∈ s (n + 1), (empiricalSet (n + 1) c : Set (Fin (n + 1) → α)))).toReal))) atTop =
    - liminf (fun n : ℕ => toEReal ((s (n + 1)).inf' (hne (n + 1) n.succ_pos) (fun c => ∑ a, ((c a : ℝ) / (n + 1)) * log (((c a : ℝ) / (n + 1)) / (μ a).toReal)))) atTop := by
  let rate : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin (n + 1) => μ.toMeasure)
      (⋃ c ∈ s (n + 1), (empiricalSet (n + 1) c : Set (Fin (n + 1) → α)))).toReal)
  let kl : ℕ → ℝ := fun n =>
    (s (n + 1)).inf' (hne (n + 1) n.succ_pos)
      (fun c => ∑ a, ((c a : ℝ) / (n + 1)) * log (((c a : ℝ) / (n + 1)) / (μ a).toReal))
  have hsum : Tendsto (fun n => rate n + kl n) atTop (nhds 0) := by
    simpa [rate, kl] using Tendsto.of.All_GtToReal_0.All_Nonempty.All_EqSum hs hne hμ
  let c : ℕ → EReal := fun n => (rate n + kl n : ℝ)
  let a : ℕ → EReal := fun n => rate n
  let b : ℕ → EReal := fun n => kl n
  have hc : Tendsto c atTop (nhds 0) := tendsto_coe.mpr hsum
  have heq : a = fun n => c n + -b n := by
    ext n
    show (rate n : EReal) = (rate n + kl n : ℝ) + - (kl n : EReal)
    rw [← EReal.coe_neg, ← EReal.coe_add, add_neg_cancel_right]
  have hsup : limsup a atTop ≤ - liminf b atTop := by
    rw [heq]
    refine (limsup_add_le (u := c) (v := fun n => -b n) ?_ ?_).trans ?_
    · exact Or.inl (by simp [hc.limsup_eq])
    · exact Or.inl (by simp [hc.limsup_eq])
    · rw [hc.limsup_eq, zero_add, show (fun n => -b n) = -b from rfl, limsup_neg]
  have hinv : -b = fun n => a n + -c n := by
    ext n
    simp only [Pi.neg_apply]
    have hn : a n = c n + -b n := congr_fun heq n
    have hsub : a n - (rate n + kl n) = -b n := by
      rw [hn]
      simpa [c] using EReal.add_sub_cancel_left (a := -b n) (b := rate n + kl n)
    rw [← hsub, sub_eq_add_neg]
    simp [c]
  apply le_antisymm hsup
  rw [← limsup_neg, hinv]
  refine (limsup_add_le (u := a) (v := fun n => -c n) ?_ ?_).trans ?_
  · exact Or.inr (by simp [show (fun n => -c n) = -c from rfl, limsup_neg, hc.liminf_eq])
  · exact Or.inr (by simp [show (fun n => -c n) = -c from rfl, limsup_neg, hc.liminf_eq])
  · rw [show (fun n => -c n) = -c from rfl, limsup_neg, hc.liminf_eq, neg_zero, add_zero]

/--
For i.i.d. samples on a finite alphabet, the limsup of `(1/n) log` of the probability of a
nonempty union of empirical types equals `-liminf` of the infimum relative entropy of those types.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {s : ℕ → Finset (α → ℕ)} {μ : PMF α}
-- given
  (hs : ∀ n, 0 < n → ∀ c ∈ s n, ∑ a, c a = n)
  (hne : ∀ n, 0 < n → (s n).Nonempty)
  (hμ : ∀ n, 0 < n → ∀ c ∈ s n, ∀ a, 0 < c a → 0 < (μ a).toReal) :
-- imply
  limsup (fun n : ℕ => toEReal (((n + 1 : ℕ) : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin (n + 1) => μ.toMeasure) (⋃ c ∈ s (n + 1), (empiricalSet (n + 1) c : Set (Fin (n + 1) → α)))).toReal))) atTop =
    - liminf (fun n : ℕ => toEReal ((s (n + 1)).inf' (hne (n + 1) n.succ_pos) (fun c => ∑ a, ((c a : ℝ) / (n + 1)) * log (((c a : ℝ) / (n + 1)) / (μ a).toReal)))) atTop :=
-- proof
  limsup_eq_neg_liminf hs hne hμ


-- created on 2026-11-02
