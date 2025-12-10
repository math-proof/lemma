import sympy.Basic


@[main, comm]
private lemma main
  [DivisionMonoid α]
-- given
  (a b : α) :
-- imply
  (a / b)⁻¹ = b / a := 
-- proof
  inv_div a b


-- created on 2025-12-08
