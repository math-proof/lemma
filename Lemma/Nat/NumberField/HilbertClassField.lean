import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.HilbertClassField
open scoped NumberField
open NumberField


/--
[IsHilbertClassField.apply_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/HilbertClassField.lean)
-/
@[path]
private lemma IsHilbertClassField_apply_maximal_eq
  {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {M : Type u} [Field M] [NumberField M] [Algebra K M]
-- given
  (h : IsHilbertClassField K L)
  (hfin : FiniteDimensional K M)
  (hgal : IsAbelianGalois K M)
  (hfinU : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal)
  (hinfU : IsUnramifiedAtInfinitePlaces K M) :
-- imply
  Nonempty (M →ₐ[K] L) := by
-- proof
  apply NumberField.IsHilbertClassField.apply_maximal h hfin hgal hfinU hinfU


-- created on 2026-10-20
