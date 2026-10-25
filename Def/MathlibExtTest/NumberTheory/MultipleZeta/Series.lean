/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Series.lean -/


import Mathlib.Tactic.FinCases
import Def.NumberTheory.MultipleZeta.Series.Part3
import Lemma.Nat.MultipleZeta.Series


namespace MetaMathlibExt.MultipleZeta

def admissibleIndex : Index :=
  ⟨2, ⟨[2], by simp, by simp⟩⟩

def nonadmissibleIndex : Index :=
  ⟨1, ⟨[1], by simp, by simp⟩⟩

def depthTwoIndex : Index :=
  ⟨3, ⟨[2, 1], by simp, by decide⟩⟩

def mOne : StrictDecreasingTuple 1 :=
  ⟨fun _ => ⟨1, by decide⟩, by
    intro i j hij
    fin_cases i
    fin_cases j
    exact (lt_irrefl 0 hij).elim⟩

def mTwo : StrictDecreasingTuple 2 :=
  ⟨![⟨2, by decide⟩, ⟨1, by decide⟩], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

end MetaMathlibExt.MultipleZeta
