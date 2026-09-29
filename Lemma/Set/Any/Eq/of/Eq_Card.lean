import Mathlib.Data.Finset.Sort
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
  {S : Finset (Fin k → ℤ)}
-- given
  (h : S.card = n) :
-- imply
  ∃ x : ℕ → Fin k → ℤ, (∀ i < n, ∀ j < i, x i ≠ x j) ∧ S = (Finset.range n).image x := by
-- proof
  subst h
  let x : ℕ → Fin k → ℤ := fun m => if hm : m < S.card then (S.equivFin.symm ⟨m, hm⟩).val else 0
  have hx : ∀ m (hm : m < S.card), x m = (S.equivFin.symm ⟨m, hm⟩).val := fun m hm => dif_pos hm
  refine ⟨x, fun i hi j hj e => ?_, ?_⟩
  · rw [hx i hi, hx j (by omega)] at e
    have := S.equivFin.symm.injective (Subtype.ext e)
    simp only [Fin.mk.injEq] at this
    omega
  · ext v
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · intro hv
      refine ⟨S.equivFin ⟨v, hv⟩, (S.equivFin ⟨v, hv⟩).isLt, ?_⟩
      rw [hx _ (S.equivFin ⟨v, hv⟩).isLt]
      simp
    · rintro ⟨m, hm, rfl⟩
      rw [hx m hm]
      exact (S.equivFin.symm ⟨m, hm⟩).property


@[main]
private lemma real
  {n : ℕ}
  {S : Finset ℝ}
-- given
  (h : S.card = n) :
-- imply
  ∃ x : ℕ → ℝ, (∀ k ∈ Finset.Ico 1 n, x (k - 1) < x k) ∧ S = (Finset.range n).image x := by
-- proof
  let x : ℕ → ℝ := fun m => if hm : m < n then S.orderEmbOfFin h ⟨m, hm⟩ else 0
  have hx : ∀ m (hm : m < n), x m = S.orderEmbOfFin h ⟨m, hm⟩ := fun m hm => dif_pos hm
  refine ⟨x, fun k hk => ?_, ?_⟩
  · rw [Finset.mem_Ico] at hk
    rw [hx k hk.2, hx (k - 1) (by omega)]
    exact (S.orderEmbOfFin h).strictMono (Fin.mk_lt_mk.mpr (by omega))
  · ext v
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · intro hv
      have hr : v ∈ Set.range (S.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact hv
      obtain ⟨m, rfl⟩ := hr
      exact ⟨m, m.isLt, by rw [hx m m.isLt]⟩
    · rintro ⟨m, hm, rfl⟩
      rw [hx m hm]
      exact Finset.orderEmbOfFin_mem S h _


@[main]
private lemma two
  {k : ℕ}
  {S : Finset (Fin k → ℤ)}
-- given
  (h : S.card = 2) :
-- imply
  ∃ x y, x ≠ y ∧ S = {x, y} := by
-- proof
  exact Finset.card_eq_two.mp h


-- created on 2026-09-27
