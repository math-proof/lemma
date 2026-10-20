import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Lie.Ado
open LieAlgebra
open scoped TensorProduct
open MathlibExt.Algebra.Lie.LandmarkWanted


/--
[ado](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma ado_eq
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  ∃ (n : ℕ) (ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
    Function.Injective ρ := by
-- proof
  apply MathlibExt.Algebra.Lie.LandmarkWanted.ado


-- created on 2026-10-20
