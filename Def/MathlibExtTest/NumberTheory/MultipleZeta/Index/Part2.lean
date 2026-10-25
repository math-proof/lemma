/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Index.lean -/


import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index
import Theorem.MathlibExtTest.NumberTheory.MultipleZeta.Index


namespace MetaMathlibExt.MultipleZeta

def one : PNat := ⟨1, Nat.zero_lt_succ 0⟩

def two : PNat := ⟨2, Nat.zero_lt_succ 1⟩

end MetaMathlibExt.MultipleZeta
