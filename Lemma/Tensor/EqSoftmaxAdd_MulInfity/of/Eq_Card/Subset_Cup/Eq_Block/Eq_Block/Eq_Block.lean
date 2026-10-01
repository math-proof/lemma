import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma relative_distance.lower_triangle
  {n m d_z : ℕ}
  {dm : Fin m → Fin n}
  {c : ℤ}
  {r : Fin n → ℤ}
  {wV : ℤ → Fin d_z → ℝ}
  {Q : Fin n → Fin d_z → ℝ}
  {K : Fin m → Fin d_z → ℝ}
  {V : Fin n → Fin m → Fin d_z → ℝ}
-- given
  (_h₀ : (Finset.univ.image dm).card = m)
  (_h₁ : ∀ i j t, V i j t = wV (c + max (-c) (min (r (dm j) - r i) c)) t) :
-- imply
  ∀ i j t, maskedSoftmax (fun j => (∑ s, Q i s * K j s) + V i j t) (fun j => if i.val < (dm j).val then 1 else 0) j = V i j t := by
-- proof
  -- sorry: py is prove(proved=False); it equates softmax of the (n, m) logits with the (n, m, d_z) tensor V itself,
  -- which is not a meaningful identity (false in general); transcribed entrywise and left unproved
  sorry


-- created on 2026-09-27
