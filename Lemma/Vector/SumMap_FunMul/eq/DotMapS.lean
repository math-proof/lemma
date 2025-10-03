import Lemma.Vector.All_EqSumMap_FunMul__DotMapS
open Vector


@[main]
private lemma main
  [Add β] [Zero β] [Mul β]
  {s : List.Vector α n}
  {f₁ f₂ : α → β} :
-- imply
  (s.map fun x => (f₁ x) * (f₂ x)).sum = (s.map f₁) ⬝ (s.map f₂) :=
-- proof
  All_EqSumMap_FunMul__DotMapS


-- created on 2024-07-01
