import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma mask.cross_attention
  {n h : ℕ}
  {a Ξ : Fin n → Fin n → ℝ}
-- given
  (h_Ξ : Ξ = fun i j => (if i = j then 1 else 0) + if (i.val < h ↔ j.val < h) then 0 else 1) :
-- imply
  (fun i j => maskedExp (a i j) (Ξ i j)) = fun i j => Ξ i j * Real.exp (a i j) := by
-- proof
  subst h_Ξ
  funext i j
  by_cases hij : i = j
  ·
    subst hij
    simp [maskedExp]
  ·
    by_cases hc : (i.val < h ↔ j.val < h)
    ·
      simp [maskedExp, hij, hc]
    ·
      simp [maskedExp, hij, hc]


-- created on 2026-09-27
