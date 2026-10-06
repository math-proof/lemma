import Lemma.Real.Sup.eq.Add_Mul.of.Gt_0.Lt
import Lemma.Real.Sup.eq.Add_Mul.of.Lt_0.Lt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m M a b : ℝ}
-- given
  (h : m < M) :
-- imply
  sSup ((fun x : ℝ => a * x + b) '' Set.Ioo m M) =
    max (a * m + b) (a * M + b) := by
-- proof
  by_cases ha : 0 < a
  · rw [Real.Sup.eq.Add_Mul.of.Gt_0.Lt ha h, max_eq_right]
    linarith [mul_lt_mul_of_pos_left h ha]
  · by_cases ha' : a < 0
    · rw [Real.Sup.eq.Add_Mul.of.Lt_0.Lt ha' h, max_eq_left]
      linarith [mul_lt_mul_of_neg_left h ha']
    · have ha0 : a = 0 := by linarith
      have hm : (m + M) / 2 ∈ Set.Ioo m M := by
        constructor <;> linarith
      have hs : (fun _ : ℝ => b) '' Set.Ioo m M = {b} := by
        ext y
        simp only [Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro ⟨x, _, rfl⟩
          rfl
        · intro hy
          exact ⟨(m + M) / 2, hm, hy.symm⟩
      simp only [ha0, zero_mul, zero_add]
      rw [hs]
      simp


-- created on 2019-12-25
