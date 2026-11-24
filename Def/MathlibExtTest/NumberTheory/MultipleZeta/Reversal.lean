module
public import Mathlib.Tactic.FinCases
public import Def.NumberTheory.MultipleZeta.Reversal.Part2
public import Theorem.Nat.MultipleZeta.Reversal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Reversal.lean -/
/-!
Tests for `MathlibExt.NumberTheory.MultipleZeta.Reversal`.
-/
namespace MetaMathlibExt.MultipleZeta

def oneEntryIndex : Index :=
  ⟨2, ⟨[2], by simp, by simp⟩⟩

def twoEntryIndex : Index :=
  ⟨3, ⟨[1, 2], by simp, by simp⟩⟩

def increasingTupleTwo : StrictIncreasingTuple 2 :=
  ⟨![⟨1, by decide⟩, ⟨2, by decide⟩], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

end MetaMathlibExt.MultipleZeta
