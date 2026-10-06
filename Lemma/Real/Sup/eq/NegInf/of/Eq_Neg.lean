import Lemma.Real.Sup.eq.Neg.Inf
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m M : ℝ}
  {f : ℝ → ℝ}
-- given
  (hf : ∀ x, f x = -f (-x)) :
-- imply
  sSup (f '' Set.Ioo (-M) (-m)) = -sInf (f '' Set.Ioo m M) := by
-- proof
  have hs : f '' Set.Ioo (-M) (-m) =
      (fun x => -f x) '' Set.Ioo m M := by
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
  have h6 := Real.Sup.eq.Neg.Inf (S := Set.Ioo m M) (f := fun x => -f x)
  simp only [neg_neg] at h6
  exact h6


-- created on 2019-04-12
