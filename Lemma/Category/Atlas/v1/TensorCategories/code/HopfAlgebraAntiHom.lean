import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraAntiHom
open Coalgebra HopfAlgebra LinearMap
open scoped TensorProduct


/--
[Corollary_1_22_6_right_dual_action_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraAntiHom.lean)
-/
@[path]
lemma Corollary_1_22_6_right_dual_action_one
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
  Corollary_1_22_6_right_dual_action (k := k) (H := H) 1 f = f := by
-- proof
  ext v
  simp [Corollary_1_22_6_right_dual_action, Corollary_1_22_6_smul_map]

/--
[Corollary_1_22_6_right_dual_action_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraAntiHom.lean)
-/
@[path]
lemma Corollary_1_22_6_right_dual_action_mul
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
  Corollary_1_22_6_right_dual_action (k := k) (a * b) f = Corollary_1_22_6_right_dual_action (k := k) a (Corollary_1_22_6_right_dual_action (k := k) b f) := by
-- proof
  ext v
  simp only [Corollary_1_22_6_right_dual_action, Corollary_1_22_6_smul_map,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [HopfAlgebra.antipode_mul_anti]
  rw [mul_smul]

/--
[Corollary_1_22_6_right_dual_action_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraAntiHom.lean)
-/
@[path]
lemma Corollary_1_22_6_right_dual_action_add
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
  Corollary_1_22_6_right_dual_action (k := k) (a + b) f = Corollary_1_22_6_right_dual_action (k := k) a f + Corollary_1_22_6_right_dual_action (k := k) b f := by
-- proof
  ext v
  simp only [Corollary_1_22_6_right_dual_action, Corollary_1_22_6_smul_map,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    map_add, add_smul]


-- created on 2026-10-23
