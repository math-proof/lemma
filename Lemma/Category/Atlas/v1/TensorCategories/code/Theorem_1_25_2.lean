import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2
open Coalgebra HopfAlgebra
open scoped TensorProduct


/--
[Theorem_1_25_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_25_2.lean)
-/
@[path]
lemma Theorem_1_25_2
  {k : Type u}
  [Field k]
  {A : Type v}
  [Ring A]
  [HopfAlgebra k A]
  [h : QuantumSl2 k A] :
-- imply
  (comul (R := k) h.K = h.K ⊗ₜ[k] h.K) ∧ (comul (R := k) h.E = h.E ⊗ₜ[k] h.K + 1 ⊗ₜ[k] h.E) ∧ (comul (R := k) h.F = h.F ⊗ₜ[k] 1 + h.Kinv ⊗ₜ[k] h.F) ∧ (comul (R := k) h.Kinv = h.Kinv ⊗ₜ[k] h.Kinv) ∧ (counit (R := k) h.K = (1 : k)) ∧ (counit (R := k) h.E = (0 : k)) ∧ (counit (R := k) h.F = (0 : k)) ∧ (counit (R := k) h.Kinv = (1 : k)) ∧ (antipode k h.K = h.Kinv) ∧ (antipode k h.E = -(h.E * h.Kinv)) ∧ (antipode k h.F = -(h.K * h.F)) ∧ (antipode k h.Kinv = h.K) :=
-- proof
  QuantumSl2.Theorem_1_25_2_Uq_sl2_Hopf


-- created on 2026-10-23
