import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
import Def.Analysis.MeasureTheory.Section_1_1_3.Part3
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/


/-- The Riemann sum difference when changing one tag -/
lemma TaggedPartition.RiemannSum_changeTag_sub {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n)
    (f: ℝ → ℝ) (k: Fin n) (t: ℝ) (ht: P.x k.castSucc ≤ t ∧ t ≤ P.x k.succ) :
    (P.changeTag k t ht).RiemannSum f - P.RiemannSum f = (f t - f (P.x_tag k)) * P.delta k := by
  -- delta is unchanged by changeTag since x is unchanged
  have h_delta : ∀ i, (P.changeTag k t ht).delta i = P.delta i := fun _ => rfl
  unfold TaggedPartition.RiemannSum
  rw [← Finset.sum_sub_distrib]
  have h_terms : ∀ i, f ((P.changeTag k t ht).x_tag i) * (P.changeTag k t ht).delta i - f (P.x_tag i) * P.delta i =
      if i = k then (f t - f (P.x_tag k)) * P.delta k else 0 := by
    intro i
    rw [h_delta]
    simp only [TaggedPartition.changeTag]
    by_cases hik : i = k
    · subst hik; simp only [Function.update_self, if_true]; ring
    · simp only [Function.update_of_ne hik, hik, if_false]; ring
  conv_lhs => rw [Finset.sum_congr rfl (fun i _ => h_terms i)]
  rw [Finset.sum_ite_eq' Finset.univ k]
  simp

/-- For a uniform partition, delta is constant -/
lemma TaggedPartition.uniform_delta {I: BoundedInterval} {n: ℕ} (hn: n > 0) (hI: I = Icc I.a I.b)
    (hab: I.a < I.b) (i: Fin n) :
    (TaggedPartition.uniform I n hn hI hab).delta i = (I.b - I.a) / n := by
  unfold TaggedPartition.delta TaggedPartition.uniform
  simp only
  rw [Fin.val_succ, show i.castSucc.val = i.val from rfl]
  field_simp
  push_cast; ring

