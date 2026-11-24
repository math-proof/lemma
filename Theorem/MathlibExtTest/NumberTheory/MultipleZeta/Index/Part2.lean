module
public import Theorem.NumberTheory.MultipleZeta.Index.Part2
public import Theorem.Nat.MultipleZeta.Index
public import Def.MathlibExtTest.NumberTheory.MultipleZeta.Index.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Index.lean -/
namespace MetaMathlibExt.MultipleZeta

example : FreeMonoid.toList (hoffmanBlock one) = [true] := by
  simp [one]

example : FreeMonoid.toList (hoffmanBlock two) = [false, true] := by
  simp [two]

example (k : PNat) : 0 < k.val := k.property

example (k : PNat) :
    hoffmanBlock k =
      (FreeMonoid.of false) ^ (k.val - 1) * FreeMonoid.of true := by
  rw [hoffmanBlock, FreeMonoid.ofList_append, ofList_replicate,
    FreeMonoid.ofList_singleton]

end MetaMathlibExt.MultipleZeta
