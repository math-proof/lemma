import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourWeightedConvolution
open Finset StatMech StatMech.FrontierD


/--
[fintypeWeightedGradeConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourWeightedConvolution.lean)
-/
@[path]
private lemma fintypeWeightedGradeConvolution_eq
  [Fintype A]
  [Fintype B]
  {gradeA : A → Nat}
  {gradeB : B → Nat}
  {weightA : A → Nat}
  {weightB : B → Nat}
  {total : Nat} :
-- imply
  (∑ a, ∑ b, if gradeA a + gradeB b = total then weightA a * weightB b else 0) = ∑ k : Fin (total + 1), (∑ a, if gradeA a = k.val then weightA a else 0) * (∑ b, if gradeB b = total - k.val then weightB b else 0) := by
-- proof
  apply StatMech.FrontierD.fintypeWeightedGradeConvolution gradeA gradeB weightA weightB total

/--
[sixVertexFourTableProduct_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourWeightedConvolution.lean)
-/
@[path]
private lemma sixVertexFourTableProduct_explicit_eq
  {index0 index1 index2 index3 : Fin 16} :
-- imply
  (∏ j, sixVertexFourHorizontalTransitionCount ((![index0, index1, index2, index3] : Fin 4 → Fin 16) (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos j)) ((![index0, index1, index2, index3] : Fin 4 → Fin 16) j)) = sixVertexFourHorizontalTransitionCount index3 index0 * sixVertexFourHorizontalTransitionCount index0 index1 * sixVertexFourHorizontalTransitionCount index1 index2 * sixVertexFourHorizontalTransitionCount index2 index3 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourTableProduct_explicit index0 index1 index2 index3


-- created on 2026-10-23
