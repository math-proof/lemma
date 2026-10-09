import Mathlib.Data.Finset.Sort
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h : ∀ i < n, ∀ j < i, x i ≠ x j) :
-- imply
  ∃ y : ℕ → ℝ, (∀ i ∈ Finset.Ico 1 n, y (i - 1) < y i) ∧ (Finset.range n).image y = (Finset.range n).image x := by
-- proof
  have hinj : Set.InjOn x ↑(Finset.range n) := by
    intro a ha b hb e
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · exact h b hb a hab e.symm
    · exact h a ha b hab e
  have hc : ((Finset.range n).image x).card = n := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  let S := (Finset.range n).image x
  let y : ℕ → ℝ := fun m => if hm : m < n then S.orderEmbOfFin hc ⟨m, hm⟩ else 0
  have hy : ∀ m (hm : m < n), y m = S.orderEmbOfFin hc ⟨m, hm⟩ := fun m hm => dif_pos hm
  have mono : ∀ a b, a < b → b < n → y a < y b := by
    intro a b hab hb
    rw [hy a (by omega), hy b hb]
    exact (S.orderEmbOfFin hc).strictMono (Fin.mk_lt_mk.mpr hab)
  have himg : (Finset.range n).image y = S := by
    ext v
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [hy m hm]
      exact Finset.orderEmbOfFin_mem S hc _
    · intro hv
      have hr : v ∈ Set.range (S.orderEmbOfFin hc) := by
        rw [Finset.range_orderEmbOfFin]
        exact hv
      obtain ⟨m, rfl⟩ := hr
      exact ⟨m, m.isLt, by rw [hy m m.isLt]⟩
  refine ⟨y, fun i hi => ?_, himg⟩
  rw [Finset.mem_Ico] at hi
  exact mono (i - 1) i (by omega) hi.2


-- created on 2023-11-12
