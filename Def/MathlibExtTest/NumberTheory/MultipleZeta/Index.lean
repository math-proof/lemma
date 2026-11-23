/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Index.lean -/

module

public import Theorem.NumberTheory.MultipleZeta.Index.Part2
public import Theorem.Nat.MultipleZeta.Index

@[expose] public section

namespace MetaMathlibExt.MultipleZeta

def emptyIndex : Index :=
  ⟨0, ⟨[], by simp, by simp⟩⟩

def oneIndex : Index :=
  ⟨1, ⟨[1], by simp, by simp⟩⟩

def twoIndex : Index :=
  ⟨2, ⟨[2], by simp, by simp⟩⟩

def heightExample : Index :=
  ⟨5, ⟨[1, 2, 2], by simp, by decide⟩⟩

end MetaMathlibExt.MultipleZeta
