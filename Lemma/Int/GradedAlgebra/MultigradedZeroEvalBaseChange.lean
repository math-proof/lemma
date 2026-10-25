import Mathlib
import sympy.Basic
import Theorem.RingTheory.GradedAlgebra.MultigradedZeroEvalBaseChange
open MetaMathlibExt


/--
[MultigradedFreeModule.baseChange_mem_degreeSpan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedZeroEvalBaseChange.lean)
-/
@[path]
private lemma MultigradedFreeModule_baseChange_mem_degreeSpan_eq
  [Field K] [AddCommGroup F] [Module K F]
  {n : ℕ} [Module (MvPolynomial (Fin n) K) F]
  {free : MultigradedFreeModule K n F ι}
  {α : Fin n →₀ Int}
  {x : F}
-- given
  (hx : x ∈ free.graded.component α) :
-- imply
  letI : Algebra (MvPolynomial (Fin n) K) K := by
-- proof
  apply MetaMathlibExt.MultigradedFreeModule.baseChange_mem_degreeSpan free α hx


-- created on 2026-10-20
