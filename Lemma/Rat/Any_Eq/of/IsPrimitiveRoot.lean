import Mathlib
import sympy.Basic

open IsLocalRing Polynomial

/--
[IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension.lean)
-/
@[path]
private lemma main
  [Field K] [Algebra ℚ K] [Field L] [CharZero L]
  {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]
  {ξ : L}
-- given
  (hξ : IsPrimitiveRoot ξ n) :
-- imply
  ∃ φ : K →+* L, φ (IsCyclotomicExtension.zeta n ℚ K) = ξ := by
-- proof
  classical
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (NeZero.pos n)
  let E := hζ.embeddingsEquivPrimitiveRoots L hirr
  have hξmem : ξ ∈ primitiveRoots n L := (mem_primitiveRoots (NeZero.pos n)).mpr hξ
  let φ : K →ₐ[ℚ] L := E.symm ⟨ξ, hξmem⟩
  refine ⟨φ.toRingHom, ?_⟩
  have : (E φ : L) = φ (IsCyclotomicExtension.zeta n ℚ K) := hζ.embeddingsEquivPrimitiveRoots_apply_coe L hirr φ
  rw [show E φ = ⟨ξ, hξmem⟩ from E.apply_symm_apply _] at this
  exact this.symm


-- created on 2026-10-05
