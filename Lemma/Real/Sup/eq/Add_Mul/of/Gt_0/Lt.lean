import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m M a b : ℝ}
-- given
  (ha : 0 < a)
  (h : m < M) :
-- imply
  sSup ((fun x : ℝ => a * x + b) '' Set.Ioo m M) = a * M + b := by
-- proof
  have hs : (fun x : ℝ => a * x + b) '' Set.Ioo m M =
      Set.Ioo (a * m + b) (a * M + b) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by linarith [mul_lt_mul_of_pos_left hx.1 ha],
        by linarith [mul_lt_mul_of_pos_left hx.2 ha]⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨(y - b) / a, ?_, ?_⟩
      · have h1 : m * a < y - b := by
          rw [mul_comm m a]
          linarith
        have h2 : y - b < M * a := by
          rw [mul_comm M a]
          linarith
        have h4 : ((y - b) / a) * a = y - b :=
          div_mul_cancel₀ _ ha.ne'
        exact ⟨by nlinarith [h4], by nlinarith [h4]⟩
      · field_simp [ha.ne']; ring
  rw [hs]
  exact csSup_Ioo (by linarith [mul_lt_mul_of_pos_left h ha])


-- created on 2019-09-11
