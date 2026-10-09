import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {m M : ℝ}
  {f : ℝ → ℝ}
-- given
  (hf : ∀ x, f x = f (-x)) :
-- imply
  sSup (f '' Set.Ioo (-M) (-m)) = sSup (f '' Set.Ioo m M) := by
-- proof
  have hs : f '' Set.Ioo (-M) (-m) = f '' Set.Ioo m M := by
    ext z
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨-x, ⟨by linarith, by linarith⟩, ?_⟩
      rw [hf x]
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨-y, ⟨by linarith, by linarith⟩, ?_⟩
      rw [hf (-y)]
      congr 1
      ring
  rw [hs]


-- created on 2019-04-11
