import sympy.atlas.NumberTheory.RothAuxiliary
import sympy.Basic
open MathlibExt.NumberTheory.RothAuxiliary
open scoped Matrix


/--
[roth_ridout_coeff_zero_of_low](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α : ℝ}
  {m : ℕ}
  {r : Fin m → ℕ}
  {γ : ℝ}
  {c : RothCoeff r}
-- given
  (hker : Matrix.mulVec (rothRidoutAuxMatrix α r γ) c = 0)
  (i : RothLowIndex r γ) :
-- imply
  c i.1 = 0 := by
-- proof
  have hrow := congrFun hker
    (i, (Fin.last (rothIntegralPolynomial α).natDegree).castSucc)
  change Matrix.mulVec (rothRidoutAuxMatrix α r γ) c
    (i, (Fin.last (rothIntegralPolynomial α).natDegree).castSucc) = 0 at hrow
  simpa [Matrix.mulVec, dotProduct, rothRidoutAuxMatrix] using hrow

/--
[roth_ridout_coeff_zero_of_complement_low](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma complement
  {α : ℝ}
  {m : ℕ}
  {r : Fin m → ℕ}
  {γ : ℝ}
  {c : RothCoeff r}
-- given
  (hker : Matrix.mulVec (rothRidoutAuxMatrix α r γ) c = 0)
  (i : RothLowIndex r γ) :
-- imply
  c (rothRidoutBoxComplement r i.1) = 0 := by
-- proof
  have hrow := congrFun hker
    (i, Fin.last ((rothIntegralPolynomial α).natDegree + 1))
  change Matrix.mulVec (rothRidoutAuxMatrix α r γ) c
    (i, Fin.last ((rothIntegralPolynomial α).natDegree + 1)) = 0 at hrow
  simpa [Matrix.mulVec, dotProduct, rothRidoutAuxMatrix] using hrow


-- created on 2026-10-21
