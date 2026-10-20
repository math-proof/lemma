import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ModularForms.JacobiTheta.JacobiCubeEulerProduct
open MetaMathlibExt.QPochhammer


/--
[jacobi_cube_euler_product_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma jacobi_cube_euler_product_hasSum_eq
  {q : Complex}
-- given
  (hq : ‖q‖ < 1) :
-- imply
  HasSum (fun n : Nat => (-1 : Complex) ^ n * ((2 * n + 1 : Nat) : Complex) *
    q ^ (n * (n + 1) / 2)) ((qPochhammerInf q q hq) ^ 3) := by
-- proof
  apply MetaMathlibExt.QPochhammer.jacobi_cube_euler_product_hasSum q hq


-- created on 2026-10-20
