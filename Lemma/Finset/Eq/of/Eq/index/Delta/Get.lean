import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → ℕ}
  {i j : Fin n}
-- given
  (h : Finset.univ.image x = Finset.range n) :
-- imply
  (if x i = x j then (1 : ℤ) else 0) = if i = j then 1 else 0 := by
-- proof
  have hinj : Function.Injective x := by
    have hc : (Finset.univ.image x).card = (Finset.univ : Finset (Fin n)).card := by
      rw [h, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    exact fun u v e => Finset.card_image_iff.mp hc (Finset.mem_coe.mpr (Finset.mem_univ u)) (Finset.mem_coe.mpr (Finset.mem_univ v)) e
  by_cases hij : i = j
  · rw [if_pos hij, if_pos (congrArg x hij)]
  · rw [if_neg hij, if_neg (fun e => hij (hinj e))]


-- created on 2020-10-24
