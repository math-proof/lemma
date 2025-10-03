import Lemma.Vector.SumMapVal.eq.SumMap
import Lemma.List.SumMap_FunMul.eq.MulSumMap
open List Vector


@[main]
private lemma main
  [Add β] [MulZeroClass β] [RightDistribClass β]
  {s : List.Vector α n}
  {f : α → β}
  {const : β} :
-- imply
  (s.map fun x => (f x) * const).sum = (s.map f).sum * const := by
-- proof
  have h : (s.val.map fun x => (f x) * const).sum = (s.val.map f).sum * const := SumMap_FunMul.eq.MulSumMap
  have h' : (s.map fun x => (f x) * const).sum = (s.val.map fun x => (f x) * const).sum := SumMapVal.eq.SumMap
  have h'' : (s.map f).sum = (s.val.map f).sum := SumMapVal.eq.SumMap
  rw [h', h'', h]


-- created on 2025-10-03
