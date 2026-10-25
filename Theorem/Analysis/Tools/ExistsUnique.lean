import Mathlib
import Def.Analysis.Tools.ExistsUnique


theorem ExistsUnique.choose_spec {α: Sort*} {p: α → Prop} (h : ∃! x, p x) :
  p h.choose := h.exists.choose_spec

theorem ExistsUnique.choose_eq {α: Sort*} {p: α → Prop} (h : ∃! x, p x) {x : α} (hx : p x) :
  h.choose = x := h.unique h.choose_spec hx

theorem ExistsUnique.choose_iff {α: Sort*} {p: α → Prop} (h : ∃! x, p x) (x : α):
  p x ↔ x = h.choose :=
  ⟨ by intro hx; exact (h.choose_eq hx).symm, by rintro rfl; exact h.choose_spec ⟩

theorem ExistsUnique.choose_eq_choose {α: Sort*} {p: α → Prop} (h : ∃! x, p x) : Exists.choose h = h.choose := by
  rw [←choose_iff]; exact (Exists.choose_spec h).1

