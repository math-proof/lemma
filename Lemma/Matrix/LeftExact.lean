import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.LeftExact
open LinearMap


/--
[exact_and_surjective_iff_forall_lcomp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/LeftExact.lean)
-/
@[path]
private lemma exact_and_surjective_iff_forall_lcomp_eq
  {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type w} [AddCommGroup P] [Module R P]
  {φ : M →ₗ[R] N}
  {ψ : N →ₗ[R] P} :
-- imply
  (Function.Exact φ ψ ∧ Function.Surjective ψ) ↔
      ∀ (D : Type w) [AddCommGroup D] [Module R D],
        Function.Injective (lcomp R D ψ) ∧
        Function.Exact (lcomp R D ψ) (lcomp R D φ) := by
-- proof
  apply LinearMap.exact_and_surjective_iff_forall_lcomp φ ψ


-- created on 2026-10-20
