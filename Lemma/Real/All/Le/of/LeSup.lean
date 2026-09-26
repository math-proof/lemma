import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  {α : Type*} [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
  {f : α → α}
  {m M : α}
-- given
  (hm : m < M)
  (hb : BddAbove (f '' Set.Ioo m M))
  (h : sSup (f '' Set.Ioo m M) ≤ M) :
-- imply
  ∀ x ∈ Set.Ioo m M, f x ≤ M := by
-- proof
  intro x hx
  apply (csSup_le_iff hb ((Set.nonempty_Ioo.mpr hm).image _)).mp h
  exact Set.mem_image_of_mem f hx


-- created on 2026-09-26
