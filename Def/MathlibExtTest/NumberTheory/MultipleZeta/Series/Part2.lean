/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Series.lean -/


import Mathlib.Tactic.FinCases
import Def.NumberTheory.MultipleZeta.Series.Part3
import Lemma.Nat.MultipleZeta.Series
import Theorem.MathlibExtTest.NumberTheory.MultipleZeta.Series


namespace MetaMathlibExt.MultipleZeta

def mWeakTwo : WeaklyDecreasingTuple 2 :=
  ⟨fun _ => ⟨1, by decide⟩, fun _ _ _ => le_rfl⟩

end MetaMathlibExt.MultipleZeta
