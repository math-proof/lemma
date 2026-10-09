import Mathlib.Topology.Order.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {m M a b c : ℝ}
-- given
  (ha : 0 < a)
  (h : m < M) :
-- imply
  sSup ((fun x : ℝ => a * x ^ 2 + b * x + c) '' Set.Ioo m M) =
    max (a * m ^ 2 + b * m + c) (a * M ^ 2 + b * M + c) := by
-- proof
  let f : ℝ → ℝ := fun x => a * x ^ 2 + b * x + c
  let A := f '' Set.Ioo m M
  let C := f '' Set.Icc m M
  have hne : (Set.Ioo m M).Nonempty :=
    ⟨(m + M) / 2, by linarith, by linarith⟩
  have hneA : A.Nonempty := hne.image _
  have hup : ∀ x ∈ Set.Icc m M, f x ≤ max (f m) (f M) := by
    intro x hx
    obtain ⟨hxm, hxM⟩ := hx
    set t : ℝ := (x - m) / (M - m) with htdef
    have ht0 : 0 ≤ t := by
      rw [htdef]
      exact div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := by
      rw [htdef, div_le_one (by linarith)]
      linarith
    have hx2 : x = (1 - t) * m + t * M := by
      have hd : t * (M - m) = x - m := by
        rw [htdef]
        exact div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne.symm)
      linarith
    have htnn : 0 ≤ t * (1 - t) := by nlinarith
    have hid : (1 - t) * f m + t * f M - f ((1 - t) * m + t * M) =
        a * (t * (1 - t)) * (M - m) ^ 2 := by ring
    have hconv : f x ≤ (1 - t) * f m + t * f M := by
      rw [hx2]
      have : 0 ≤ a * (t * (1 - t)) * (M - m) ^ 2 := by
        exact mul_nonneg (mul_nonneg ha.le htnn) (by positivity)
      linarith [hid, this]
    by_cases hfm : f m ≤ f M
    · have : (1 - t) * f m + t * f M ≤ f M := by nlinarith
      rw [max_eq_right hfm]
      linarith
    · have : (1 - t) * f m + t * f M ≤ f m := by nlinarith
      rw [max_eq_left (by linarith)]
      linarith
  have hbA : BddAbove A := ⟨max (f m) (f M), by
    rintro _ ⟨x, hx, rfl⟩; exact hup x ⟨hx.1.le, hx.2.le⟩⟩
  have hbC : BddAbove C := ⟨max (f m) (f M), by
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
    exact csSup_le (⟨f m, Set.mem_image_of_mem _ ⟨le_rfl, h.le⟩⟩) fun z hz =>
      le_csSup hbcl (hsub hz)
  have hm2 : f m ∈ C := Set.mem_image_of_mem _ ⟨le_rfl, h.le⟩
  have hM2 : f M ∈ C := Set.mem_image_of_mem _ ⟨h.le, le_rfl⟩
  have h2 : max (f m) (f M) ≤ sSup C := by
    rw [max_le_iff]
    exact ⟨le_csSup hbC hm2, le_csSup hbC hM2⟩
  exact le_antisymm (csSup_le hneA (by
    rintro _ ⟨x, hx, rfl⟩; exact hup x ⟨hx.1.le, hx.2.le⟩)) (h2.trans h1)


-- created on 2019-09-09
-- updated on 2025-04-20
