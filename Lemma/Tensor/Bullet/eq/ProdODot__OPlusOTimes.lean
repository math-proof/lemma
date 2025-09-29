import sympy.concrete.prefix_sum.all_prefix_sums
import sympy.Basic


@[main]
private lemma main
  [OPlus α]
  [OTimes α]
  [ODot α]
  [Bullet α]
  {cᵢ c_j : α × α} :
-- imply
  cᵢ • c_j = ⟨cᵢ.fst ⊙ c_j.fst, (cᵢ.snd ⊗ c_j.fst) ⊕ c_j.snd⟩ :=
-- proof
  Bullet.property cᵢ c_j


-- created on 2024-12-08
