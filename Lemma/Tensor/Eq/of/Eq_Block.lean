import sympy.Basic
import sympy.functions.elementary.masked_softmax


@[main]
private lemma double_integer_embedding
  {h m i : ℕ}
  {AX : ℕ → Fin (m + m) → ℝ}
  {AL AH : ℕ → Fin m → ℝ}
-- given
  (h₀ : h > 0)
  (h₁ : ∀ i, AX i = Fin.append (AL (i / h % h)) (AH (i % h))) :
-- imply
  AX (i + h * h) = AX i := by
-- proof
  rw [h₁, h₁, Nat.add_mul_div_right _ _ h₀, Nat.add_mod_right, Nat.add_mul_mod_self_right]


@[main]
private lemma mask.cross_attention
  {n h : ℕ}
  {a Ξ : Fin n → Fin n → ℝ}
-- given
  (h_Ξ : Ξ = fun i j => if (i.val < h ↔ j.val < h) then 0 else 1) :
-- imply
  (fun i j => maskedExp (a i j) (Ξ i j)) = fun i j => Ξ i j * Real.exp (a i j) := by
-- proof
  subst h_Ξ
  funext i j
  by_cases hc : (i.val < h ↔ j.val < h)
  ·
    simp [maskedExp, hc]
  ·
    simp [maskedExp, hc]


-- created on 2026-09-27
-- updated on 2026-09-27
