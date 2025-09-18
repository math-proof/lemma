import Lemma.Algebra.Eq_Length_ProdConsSumMap.of.NeLength_0
open Algebra


/--
[concat](https://pytorch.org/docs/stable/generated/torch.concat.html)
here, we assume that torch.concat is only called with dim = 0 with torch.cat
-/
def concat
  [Inhabited α]
  (s : List (Tensor α shape)) :
  Tensor α (shape.headD 1 * s.length :: shape.tail) :=
  if h : s.length ≠ 0 then
    ⟨
      (s.map (fun t => t.data.val)).flatten,
      (Eq_Length_ProdConsSumMap.of.NeLength_0 h).symm
    ⟩
  else
    default
