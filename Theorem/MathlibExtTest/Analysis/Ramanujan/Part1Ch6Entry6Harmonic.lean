/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch6Entry6Harmonic
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 6 API checks

Partial sums at `0` and successors, values of the extension at `0`, `1`, `1/2` and naturals, the
first derivative at the origin, and the Taylor expansion.
-/


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch6Entry6Harmonic

open MathlibExt.Analysis.Ramanujan.Part1Ch6.Entry6Harmonic

open scoped ContDiff

-- Partial sums at `0`, `1` and `3`.
example (f : ℝ → ℝ) : chapter6PartialSum f 0 = 0 := by simp

example (f : ℝ → ℝ) : chapter6PartialSum f 1 = f 1 := by simp

example (f : ℝ → ℝ) : chapter6PartialSum f 3 = f 1 + f 2 + f 3 := by norm_num

-- The extension vanishes at `0`, and the difference equation gives `F 1 = f 1`.
example (f : ℝ → ℝ) : chapter6ConvergentSumExtension f 0 = 0 := by simp

example (f : ℝ → ℝ) (h : Summable (chapter6ShiftedDerivedSeriesTerm f 0 0)) :
    chapter6ConvergentSumExtension f 1 = f 1 := by
  simpa using chapter6ConvergentSumExtension_sub_sub_one f 1 (by simpa using h)

-- The difference equation at a non-integer point.
example (f : ℝ → ℝ) (h : Summable (chapter6ShiftedDerivedSeriesTerm f 0 (-1 / 2))) :
    chapter6ConvergentSumExtension f (1 / 2) - chapter6ConvergentSumExtension f (-1 / 2) =
      f (1 / 2) := by
  have := chapter6ConvergentSumExtension_sub_sub_one f (1 / 2) (by convert h using 2; norm_num)
  norm_num at this ⊢
  exact this

-- Agreement with the partial sum at `2`.
example (f : ℝ → ℝ) (h : Summable (chapter6ShiftedDerivedSeriesTerm f 0 0)) :
    chapter6ConvergentSumExtension f 2 = f 1 + f 2 := by
  simpa [one_add_one_eq_two] using chapter6ConvergentSumExtension_natCast f h 2

-- The first derivative at the origin is `-∑ f'(k + 1)`.
example (f : ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho) (hsmooth : ContDiff ℝ ∞ f)
    (hsummable : ∀ q : ℕ, Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
    (hdominated : ∀ q : ℕ, 0 < q → ∃ bound : ℕ → ℝ, Summable bound ∧
      ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ, |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k) :
    deriv (chapter6ConvergentSumExtension f) 0 = -chapter6DerivedSeriesConstant f 1 := by
  rw [← iteratedDeriv_one]
  exact iteratedDeriv_chapter6ConvergentSumExtension_apply_zero f rho hrho hsmooth hsummable
    hdominated 1 one_pos

-- Near the origin the extension equals the `tsum` of its Taylor terms.
example (f : ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho) (hsmooth : ContDiff ℝ ∞ f)
    (hsummable : ∀ q : ℕ, Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
    (hdominated : ∀ q : ℕ, 0 < q → ∃ bound : ℕ → ℝ, Summable bound ∧
      ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ, |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
    (hanalytic : AnalyticAt ℝ (chapter6ConvergentSumExtension f) 0) :
    ∃ r > 0, ∀ x : ℝ, |x| < r →
      ∑' j, chapter6Entry6Term f x j = chapter6ConvergentSumExtension f x := by
  obtain ⟨r, hr, -, h⟩ :=
    exists_hasSum_chapter6Entry6Term f rho hrho hsmooth hsummable hdominated hanalytic
  exact ⟨r, hr, fun x hx => (h x hx).tsum_eq⟩

end MathlibExtTest.Analysis.Ramanujan.Part1Ch6Entry6Harmonic
