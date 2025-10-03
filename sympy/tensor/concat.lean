import Lemma.Tensor.Eq_Length_ProdConsSumMap.of.NeLength_0
open Tensor


/--
[concat](https://pytorch.org/docs/stable/generated/torch.concat.html)
here, we assume that torch.concat is only called with dim = 0 with torch.cat
-/
def concat
  [Inhabited α]
  (shape : List (Tensor α s)) :
  Tensor α (s.headD 1 * shape.length :: s.tail) :=
  if h : shape.length ≠ 0 then
    ⟨
      (shape.map (fun t => t.data.val)).flatten,
      (Eq_Length_ProdConsSumMap.of.NeLength_0 h).symm
    ⟩
  else
    default
