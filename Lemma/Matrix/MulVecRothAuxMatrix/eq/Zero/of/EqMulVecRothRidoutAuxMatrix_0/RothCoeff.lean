import sympy.atlas.NumberTheory.RothAuxiliary
import sympy.Basic
open MathlibExt.NumberTheory.RothAuxiliary
open scoped Matrix


/--
[roth_ridout_old_mulVec_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α : ℝ}
  {m : ℕ}
  {r : Fin m → ℕ}
  {γ : ℝ}
  {c : RothCoeff r}
-- given
  (hker : Matrix.mulVec (rothRidoutAuxMatrix α r γ) c = 0) :
-- imply
  Matrix.mulVec (rothAuxMatrix α r γ) c = 0 := by
-- proof
  funext u
  obtain ⟨i, k⟩ := u
  have hrow := congrFun hker (i, k.castSucc.castSucc)
  change Matrix.mulVec (rothRidoutAuxMatrix α r γ) c
    (i, k.castSucc.castSucc) = 0 at hrow
  simpa [Matrix.mulVec, dotProduct, rothRidoutAuxMatrix] using hrow


-- created on 2026-10-21
