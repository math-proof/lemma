import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m M a b : ℝ}
-- given
  (ha : a < 0)
  (h : m < M) :
-- imply
  sSup ((fun x : ℝ => a * x + b) '' Set.Ioo m M) = a * m + b := by
-- proof
  have hs : (fun x : ℝ => a * x + b) '' Set.Ioo m M =
      Set.Ioo (a * M + b) (a * m + b) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by linarith [mul_lt_mul_of_neg_left hx.2 ha],
        by linarith [mul_lt_mul_of_neg_left hx.1 ha]⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨(y - b) / a, ?_, ?_⟩
      · exact ⟨by rw [lt_div_iff_of_neg ha]; linarith,
          by rw [div_lt_iff_of_neg ha]; linarith⟩
      · field_simp [ha.ne]; ring
  rw [hs]
  exact csSup_Ioo (by linarith [mul_lt_mul_of_neg_left h ha])


-- created on 2019-12-23
