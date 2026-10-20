import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.JordanLinearGroups
open scoped commutatorElement
open scoped Matrix.Norms.L2Operator
open scoped MatrixOrder ComplexOrder
open MathlibExt.GroupTheory.JordanLinearGroupsWanted


/--
[jordan_linear_groups](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/JordanLinearGroups.lean)
-/
@[path]
private lemma jordan_linear_groups_eq
  {n : ℕ} :
-- imply
  ∃ J : ℕ, ∀ (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) Complex)),
    Finite ↥G →
    ∃ (A : Subgroup (Matrix.GeneralLinearGroup (Fin n) Complex)),
    A ≤ G ∧
    (∀ g ∈ G, ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
    A.relIndex G ≤ J := by
-- proof
  apply MathlibExt.GroupTheory.JordanLinearGroupsWanted.jordan_linear_groups n


-- created on 2026-10-20
