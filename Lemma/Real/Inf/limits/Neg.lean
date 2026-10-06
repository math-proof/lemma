import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ} :
-- imply
  sInf (f '' Set.Ioo a b) = sInf ((fun x => f (-x)) '' Set.Ioo (-b) (-a)) := by
-- proof
  have himg : (fun x => f (-x)) '' Set.Ioo (-b) (-a) = f '' Set.Ioo a b := by
    ext z
    constructor
    ·
      rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨-x, ⟨by linarith, by linarith⟩, rfl⟩
    ·
      rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨-x, ⟨by linarith, by linarith⟩, by simp⟩
  rw [himg]


-- created on 2019-10-03
