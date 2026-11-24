module
public import Mathlib.Tactic.FinCases
public import Def.NumberTheory.MultipleZeta.Series.Part3
public import Theorem.Nat.MultipleZeta.Series
public import Def.MathlibExtTest.NumberTheory.MultipleZeta.Series.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Series.lean -/
namespace MetaMathlibExt.MultipleZeta

example : (mWeakTwo.1 ⟨0, by decide⟩ : ℕ) = 1 := rfl

example : (mWeakTwo.1 ⟨1, by decide⟩ : ℕ) = 1 := rfl

example (m : WeaklyDecreasingTuple 2) :
    (m.1 ⟨1, by decide⟩ : ℕ) ≤ (m.1 ⟨0, by decide⟩ : ℕ) :=
  m.2 (by decide)

example :
    starSummand depthTwoIndex mTwo.toWeaklyDecreasing = strictSummand depthTwoIndex mTwo :=
  starSummand_toWeaklyDecreasing depthTwoIndex mTwo

example (index : Index) (h : index.IsAdmissibleOrEmpty) :
    starValue index h =
      ∑' m : WeaklyDecreasingTuple index.depth, starSummand index m :=
  rfl

example : starSummand Index.empty WeaklyDecreasingTuple.empty = 1 :=
  starSummand_empty WeaklyDecreasingTuple.empty

example : starValue Index.empty (.inr Index.empty_depth) = 1 := by
  apply starValue_empty

end MetaMathlibExt.MultipleZeta
