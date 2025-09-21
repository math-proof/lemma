import Lemma.Basic


@[main]
private lemma main
-- given
  (h : n = 1)
  (a : List.Vector α n)
  (b : List.Vector β n)
  (f : α → β → γ):
-- imply
  a.map₂ f b = a.map fun x => f x b[0] := by
-- proof
  subst h
  have ha := a.2
  rw [List.length_eq_one_iff] at ha
  let ⟨x, hx⟩ := ha
  have hb := b.2
  rw [List.length_eq_one_iff] at hb
  let ⟨y, hy⟩ := hb
  have a_eq : a = ⟨[x], by simp⟩ := Subtype.eq hx
  have b_eq : b = ⟨[y], by simp⟩ := Subtype.eq hy
  aesop


-- created on 2025-09-21
