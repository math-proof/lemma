module
public import Mathlib.Tactic.FinCases
public import Def.NumberTheory.MultipleZeta.Series.Part3
public import Theorem.Nat.MultipleZeta.Series
public import Theorem.MathlibExtTest.NumberTheory.MultipleZeta.Series


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Series.lean -/
namespace MetaMathlibExt.MultipleZeta

def mWeakTwo : WeaklyDecreasingTuple 2 :=
  ⟨fun _ => ⟨1, by decide⟩, fun _ _ _ => le_rfl⟩

end MetaMathlibExt.MultipleZeta
