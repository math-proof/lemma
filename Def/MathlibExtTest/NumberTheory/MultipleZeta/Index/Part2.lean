/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Index.lean -/

module

public import Theorem.NumberTheory.MultipleZeta.Index.Part2
public import Theorem.Nat.MultipleZeta.Index
public import Theorem.MathlibExtTest.NumberTheory.MultipleZeta.Index

@[expose] public section

namespace MetaMathlibExt.MultipleZeta

def one : PNat := ⟨1, Nat.zero_lt_succ 0⟩

def two : PNat := ⟨2, Nat.zero_lt_succ 1⟩

end MetaMathlibExt.MultipleZeta
