import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ} :
-- imply
  sSup (f '' Set.Ioo a b) =
    sSup ((fun x => f (-x)) '' Set.Ioo (-b) (-a)) := by
-- proof
  have hs : f '' Set.Ioo a b =
      (fun x => f (-x)) '' Set.Ioo (-b) (-a) := by
    ext z
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨-x, ⟨by linarith, by linarith⟩, by congr 1; ring⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨-y, ⟨by linarith, by linarith⟩, rfl⟩
  rw [hs]


-- created on 2020-03-28
