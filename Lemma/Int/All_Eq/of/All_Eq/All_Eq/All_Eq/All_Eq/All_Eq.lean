import Mathlib
import sympy.Basic


/--
[IharaLemma_square_localized](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_square_localized.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {S : Submonoid R}
  {V Vk V' Vk' L L' Lk Lk' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup Vk] [Module R Vk] [AddCommGroup V'] [Module R V'] [AddCommGroup Vk'] [Module R Vk'] [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [AddCommGroup Lk] [Module R Lk] [AddCommGroup Lk'] [Module R Lk']
  {f : V →ₗ[R] L}
  {redV : V →ₗ[R] Vk}
  {redL : L →ₗ[R] Lk}
  {fk : Vk →ₗ[R] Lk}
  {gV : V →ₗ[R] V'} [IsLocalizedModule S gV]
  {gK : Vk →ₗ[R] Vk'} [IsLocalizedModule S gK]
  {gL : L →ₗ[R] L'}
  {gLk : Lk →ₗ[R] Lk'} [IsLocalizedModule S gLk]
  {f' : V' →ₗ[R] L'}
  {redV' : V' →ₗ[R] Vk'}
  {redL' : L' →ₗ[R] Lk'}
  {fk' : Vk' →ₗ[R] Lk'}
-- given
  (hsq : ∀ v, redL (f v) = fk (redV v))
  (hf' : ∀ v, f' (gV v) = gL (f v))
  (hredV' : ∀ v, redV' (gV v) = gK (redV v))
  (hredL' : ∀ x, redL' (gL x) = gLk (redL x))
  (hfk' : ∀ y, fk' (gK y) = gLk (fk y)) :
-- imply
  ∀ v', redL' (f' v') = fk' (redV' v') := by
-- proof
  have h : redL' ∘ₗ f' = fk' ∘ₗ redV' := by
    apply IsLocalizedModule.linearMap_ext S gV gLk
    ext v
    simp only [LinearMap.comp_apply, hf', hredL', hsq, ← hfk', hredV']
  intro v'
  exact LinearMap.congr_fun h v'


-- created on 2026-10-05
