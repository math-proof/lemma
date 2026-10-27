import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {s : Finset ℝ}
  {x t : ℝ}
-- given
  (h : x ∈ s) :
-- imply
  x + t ∈ Finset.image (fun z => z + t) s :=
-- proof
  Finset.mem_image.mpr ⟨x, h, rfl⟩


-- created on 2021-03-04
-- updated on 2026-10-26
