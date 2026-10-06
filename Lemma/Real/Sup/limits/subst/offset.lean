import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b t : ℝ}
  {f : ℝ → ℝ} :
-- imply
  sSup (f '' Set.Ioo a b) =
    sSup ((fun x => f (x - t)) '' Set.Ioo (a + t) (b + t)) := by
-- proof
  have hs : f '' Set.Ioo a b =
      (fun x => f (x - t)) '' Set.Ioo (a + t) (b + t) := by
    ext z
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨x + t, ⟨by linarith, by linarith⟩, by ring⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨y - t, ⟨by linarith, by linarith⟩, rfl⟩
  rw [hs]


-- created on 2019-08-29
