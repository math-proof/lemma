import Mathlib.Topology.Order.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m M : ℝ}
-- given
  (h : m < M) :
-- imply
  sSup ((fun x : ℝ => x ^ 2) '' Set.Ioo m M) = max (m ^ 2) (M ^ 2) := by
-- proof
  let f : ℝ → ℝ := fun x => x ^ 2
  let A := f '' Set.Ioo m M
  let C := f '' Set.Icc m M
  have hne : (Set.Ioo m M).Nonempty :=
    ⟨(m + M) / 2, by linarith, by linarith⟩
  have hneA : A.Nonempty := hne.image _
  have hneC : C.Nonempty :=
    ⟨f m, Set.mem_image_of_mem _ ⟨le_rfl, h.le⟩⟩
  have hup : ∀ x ∈ Set.Icc m M, x ^ 2 ≤ max (m ^ 2) (M ^ 2) := by
    intro x hx
    obtain ⟨hxm, hxM⟩ := hx
    by_cases hx0 : 0 ≤ x
    · have : x ^ 2 ≤ M ^ 2 := by nlinarith
      exact this.trans (le_max_right _ _)
    · have : x ^ 2 ≤ m ^ 2 := by nlinarith
      exact this.trans (le_max_left _ _)
  have hbA : BddAbove A := ⟨max (m ^ 2) (M ^ 2), by
    rintro _ ⟨x, hx, rfl⟩; exact hup x ⟨hx.1.le, hx.2.le⟩⟩
  have hbC : BddAbove C := ⟨max (m ^ 2) (M ^ 2), by
    rintro _ ⟨x, hx, rfl⟩; exact hup x hx⟩
  have hcl : closure (Set.Ioo m M) = Set.Icc m M :=
    closure_Ioo h.ne
  have hsub : C ⊆ closure A := by
    simp only [C, ←hcl]
    exact image_closure_subset_closure_image (by fun_prop)
  have hIic : closure A ⊆ Set.Iic (sSup A) :=
    closure_minimal (fun _ hz => le_csSup hbA hz) isClosed_Iic
  have hbcl : BddAbove (closure A) := ⟨sSup A, hIic⟩
  have hcs : sSup (closure A) = sSup A := by
    apply le_antisymm
    · exact csSup_le hneA.closure fun z hz => hIic hz
    · exact csSup_le hneA fun z hz =>
        le_csSup hbcl (subset_closure hz)
  have h1 : sSup C ≤ sSup A := by
    rw [←hcs]
    exact csSup_le hneC fun z hz => le_csSup hbcl (hsub hz)
  have hm2 : f m ∈ C := Set.mem_image_of_mem _ ⟨le_rfl, h.le⟩
  have hM2 : f M ∈ C := Set.mem_image_of_mem _ ⟨h.le, le_rfl⟩
  have h2 : max (m ^ 2) (M ^ 2) ≤ sSup C := by
    rw [max_le_iff]
    exact ⟨le_csSup hbC hm2, le_csSup hbC hM2⟩
  exact le_antisymm (csSup_le hneA (by
    rintro _ ⟨x, hx, rfl⟩; exact hup x ⟨hx.1.le, hx.2.le⟩)) (h2.trans h1)


-- created on 2019-09-08
