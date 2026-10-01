import sympy.sets.sets
import sympy.Basic


@[main]
private lemma limits.negate
  {f : ℝ → ℝ}
  {a b : ℝ} :
-- imply
  sSup (f '' Set.Icc a b) = sSup ((fun x => f (-x)) '' Set.Icc (-b) (-a)) := by
-- proof
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨-x, ⟨by linarith, by linarith⟩, by rw [neg_neg]⟩
  · rintro ⟨x, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨-x, ⟨by linarith, by linarith⟩, rfl⟩


@[main]
private lemma limits.subst.offset
  {f : ℝ → ℝ}
  {a b t : ℝ} :
-- imply
  sSup (f '' Set.Icc a b) = sSup ((fun x => f (x + t)) '' Set.Icc (a - t) (b - t)) := by
-- proof
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨x - t, ⟨by linarith, by linarith⟩, by rw [sub_add_cancel]⟩
  · rintro ⟨x, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨x + t, ⟨by linarith, by linarith⟩, rfl⟩


-- created on 2026-09-27
