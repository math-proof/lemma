import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n i j : ℕ}
  {x a : ℕ → ℤ}
-- given
  (h₀ : ((Finset.range n).image a).card = n)
  (h₁ : (Finset.range n).image x = (Finset.range n).image a)
  (hi : i < n)
  (hj : j < n) :
-- imply
  (if x i = x j then (1 : ℤ) else 0) = if i = j then 1 else 0 := by
-- proof
  have hc : ((Finset.range n).image x).card = (Finset.range n).card := by
    rw [h₁, h₀, Finset.card_range]
  have hinj := Finset.card_image_iff.mp hc
  if hij : i = j then
    subst hij
    simp
  else
    rw [ite_eq_right hij, ite_eq_right (fun e => hij (hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr hi))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr hj)) e))]


-- created on 2021-09-25
