import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n i j : ℕ}
  {x : Fin n → ℕ}
  {a b : Fin n}
-- given
  (h : Finset.univ.image x = Finset.range n)
  (ha : x a = i)
  (hb : x b = j) :
-- imply
  (if a = b then (1 : ℤ) else 0) = if i = j then 1 else 0 := by
-- proof
  have hinj : Function.Injective x := by
    have hc : (Finset.univ.image x).card = (Finset.univ : Finset (Fin n)).card := by
      rw [h, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    exact fun u v e => Finset.card_image_iff.mp hc (Finset.mem_coe.mpr (Finset.mem_univ u)) (Finset.mem_coe.mpr (Finset.mem_univ v)) e
  subst ha hb
  by_cases hab : a = b
  · rw [if_pos hab, if_pos (congrArg x hab)]
  · rw [if_neg hab, if_neg (fun e => hab (hinj e))]


-- created on 2020-10-25
