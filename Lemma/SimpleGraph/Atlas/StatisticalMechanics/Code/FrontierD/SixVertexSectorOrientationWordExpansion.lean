import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientationWordExpansion
open Finset Matrix StatMech StatMech.FrontierD


/--
[matrixOrientationWordProduct_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma matrixOrientationWordProduct_zero_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {B : Matrix alpha alpha Real}
-- given
  (word : Fin 0 -> Bool) :
-- imply
  matrixOrientationWordProduct B 0 word = 1 := by
-- proof
  apply StatMech.FrontierD.matrixOrientationWordProduct_zero B word

/--
[matrixOrientationWordProduct_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma matrixOrientationWordProduct_cons_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {B : Matrix alpha alpha Real}
  {M : Nat}
  {b : Bool}
-- given
  (word : Fin M -> Bool) :
-- imply
  matrixOrientationWordProduct B (M + 1) (Fin.cons b word) = (if b then B else Bᵀ) * matrixOrientationWordProduct B M word := by
-- proof
  apply StatMech.FrontierD.matrixOrientationWordProduct_cons B M b word

/--
[sum_matrixOrientationWordProduct_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma sum_matrixOrientationWordProduct_succ_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {B : Matrix alpha alpha Real}
  {M : Nat} :
-- imply
  (∑ word : Fin (M + 1) -> Bool, matrixOrientationWordProduct B (M + 1) word) = (B + Bᵀ) * ∑ word : Fin M -> Bool, matrixOrientationWordProduct B M word := by
-- proof
  apply StatMech.FrontierD.sum_matrixOrientationWordProduct_succ B M

/--
[add_transpose_pow_eq_sum_orientationWords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma add_transpose_pow_eq_sum_orientationWords_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {B : Matrix alpha alpha Real}
  {M : Nat} :
-- imply
  (B + Bᵀ) ^ M = ∑ word : Fin M -> Bool, matrixOrientationWordProduct B M word := by
-- proof
  apply StatMech.FrontierD.add_transpose_pow_eq_sum_orientationWords B M

/--
[sixVertexSectorTransfer_pow_eq_sum_orientationWords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_pow_eq_sum_orientationWords_eq
  {N n M : Nat}
  {c : Real} :
-- imply
  sixVertexSectorTransfer N n c ^ M = ∑ word : Fin M -> Bool, matrixOrientationWordProduct (sixVertexSectorForwardTransfer N n c) M word := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_pow_eq_sum_orientationWords N n M c

/--
[trace_sixVertexSectorTransfer_pow_eq_sum_orientationWords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma trace_sixVertexSectorTransfer_pow_eq_sum_orientationWords_eq
  {N n M : Nat}
  {c : Real} :
-- imply
  Matrix.trace (sixVertexSectorTransfer N n c ^ M) = ∑ word : Fin M -> Bool, Matrix.trace (matrixOrientationWordProduct (sixVertexSectorForwardTransfer N n c) M word) := by
-- proof
  apply StatMech.FrontierD.trace_sixVertexSectorTransfer_pow_eq_sum_orientationWords N n M c

/--
[trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace_eq
  {N n M : Nat}
  {c : Real} :
-- imply
  Matrix.trace (sixVertexSectorTransfer N n c ^ M) = ∑ word : Fin M -> Bool, sixVertexOrientationWordTrace N M c n word := by
-- proof
  apply StatMech.FrontierD.trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace N n M c

/--
[traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs_eq
  {N nLeft nRight M : Nat}
  {c : Real} :
-- imply
  Matrix.trace (sixVertexSectorTransfer N nLeft c ^ M) * Matrix.trace (sixVertexSectorTransfer N nRight c ^ M) = ∑ leftWord : Fin M -> Bool, ∑ rightWord : Fin M -> Bool, sixVertexOrientationWordTrace N M c nLeft leftWord * sixVertexOrientationWordTrace N M c nRight rightWord := by
-- proof
  apply StatMech.FrontierD.traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs N nLeft nRight M c

/--
[sixVertexSectorTrace_logConcave_iff_wordPairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_iff_wordPairSum_eq
  {N M n : Nat}
  {c : Real} :
-- imply
  Matrix.trace (sixVertexSectorTransfer N (n - 1) c ^ M) * Matrix.trace (sixVertexSectorTransfer N (n + 1) c ^ M) <= Matrix.trace (sixVertexSectorTransfer N n c ^ M) ^ 2 <-> (∑ leftWord : Fin M -> Bool, ∑ rightWord : Fin M -> Bool, sixVertexOrientationWordTrace N M c (n - 1) leftWord * sixVertexOrientationWordTrace N M c (n + 1) rightWord) <= ∑ leftWord : Fin M -> Bool, ∑ rightWord : Fin M -> Bool, sixVertexOrientationWordTrace N M c n leftWord * sixVertexOrientationWordTrace N M c n rightWord := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_iff_wordPairSum N M n c


-- created on 2026-10-23
