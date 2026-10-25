import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
open WalkCountFormula
open scoped Classical


namespace WalkCountFormula

/--
[iterU_liftU_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkOperatorLemmas.lean)
-/
@[path]
lemma iterU_liftU_comm
  {n : ℕ}
  {f : YoungDiagram →₀ ℤ} :
-- imply
  iterU n (liftU f) = liftU (iterU n f) := by
-- proof
  show (liftU ^ n : Module.End ℤ _) (liftU f) =
    liftU ((liftU ^ n : Module.End ℤ _) f)
  have h : (liftU ^ n : Module.End ℤ _) * liftU =
    liftU * (liftU ^ n : Module.End ℤ _) :=
    pow_mul_comm' liftU n
  show ((liftU ^ n : Module.End ℤ _) * liftU) f =
    (liftU * (liftU ^ n : Module.End ℤ _)) f
  rw [h]
end WalkCountFormula



-- created on 2026-10-23
