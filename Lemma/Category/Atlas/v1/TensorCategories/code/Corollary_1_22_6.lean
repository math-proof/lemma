import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.Corollary_1_22_6
open CategoryTheory Coalgebra HopfAlgebra LinearMap
open scoped TensorProduct


/--
[corollary_1_22_6_right_dual_action_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_22_6.lean)
-/
@[path]
lemma corollary_1_22_6_right_dual_action_one
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [HopfAlgebra k H]
  {V : Type v}
  [AddCommGroup V]
  [Module k V]
  [Module H V]
  [SMulCommClass k H V]
  {f : Module.Dual k V} :
-- imply
  corollary_1_22_6_right_dual_action (k := k) (H := H) 1 f = f := by
-- proof
  ext v
  simp [corollary_1_22_6_right_dual_action, corollary_1_22_6_smul_map]

/--
[corollary_1_22_6_right_dual_action_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_22_6.lean)
-/
@[path]
lemma corollary_1_22_6_right_dual_action_mul
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [HopfAlgebra k H]
  {V : Type v}
  [AddCommGroup V]
  [Module k V]
  [Module H V]
  [SMulCommClass k H V]
  {a b : H}
  {f : Module.Dual k V} :
-- imply
  corollary_1_22_6_right_dual_action (k := k) (a * b) f = corollary_1_22_6_right_dual_action (k := k) a (corollary_1_22_6_right_dual_action (k := k) b f) := by
-- proof
  ext v
  simp only [corollary_1_22_6_right_dual_action, corollary_1_22_6_smul_map,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [HopfAlgebra.antipode_mul_anti]
  rw [mul_smul]

/--
[corollary_1_22_6_right_dual_action_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_22_6.lean)
-/
@[path]
lemma corollary_1_22_6_right_dual_action_add
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [HopfAlgebra k H]
  {V : Type v}
  [AddCommGroup V]
  [Module k V]
  [Module H V]
  [SMulCommClass k H V]
  {a b : H}
  {f : Module.Dual k V} :
-- imply
  corollary_1_22_6_right_dual_action (k := k) (a + b) f = corollary_1_22_6_right_dual_action (k := k) a f + corollary_1_22_6_right_dual_action (k := k) b f := by
-- proof
  ext v
  simp only [corollary_1_22_6_right_dual_action, corollary_1_22_6_smul_map,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    map_add, add_smul]
section CategoricalStatements


-- created on 2026-10-23
