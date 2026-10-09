import Mathlib
import sympy.Basic


/--
[Algebra_norm_prod](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_norm_prod.lean)
-/
@[path]
private lemma main
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
  {x : A × B} :
-- imply
  Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
-- proof
  have lmul_prod : Algebra.lmul R (A × B) x
      = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2) : A × B →ₗ[R] A × B) := by
    ext y <;> rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, lmul_prod,
    LinearMap.det_prodMap]


-- created on 2026-10-03
