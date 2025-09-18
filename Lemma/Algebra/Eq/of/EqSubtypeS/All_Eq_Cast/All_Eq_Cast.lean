import Lemma.Basic


@[main]
private lemma main
  {p : α → Prop}
  {q : α → Prop}
-- given
  (h : {l // p l} = {l // q l})
  (h_all_p : ∀ (x : α) (hx : p x), x = cast h ⟨x, hx⟩)
  (h_all_q : ∀ (x : α) (hx : q x), x = cast h.symm ⟨x, hx⟩) :
-- imply
  p = q := by
-- proof
  apply funext
  intro x
  apply propext
  apply Iff.intro
  ·
    intro hx
    let qV : Subtype q := cast h ⟨x, hx⟩
    have h_eq : x = qV.val := by
      simp [qV]
      apply h_all_p x hx
    rw [h_eq]
    exact qV.property
  ·
    intro hx
    let pV : Subtype p := cast h.symm ⟨x, hx⟩
    have h_eq : x = pV.val := by
      simp [pV]
      apply h_all_q x hx
    rw [h_eq]
    exact pV.property


-- created on 2025-05-21
