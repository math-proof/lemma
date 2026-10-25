import Mathlib
import sympy.Basic
import Structure.NumberTheory.NumberField.HilbertClassField
open scoped NumberField
open NumberField


namespace NumberField

/--
[IsHilbertClassField.apply_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/HilbertClassField.lean)
-/
@[path]
lemma IsHilbertClassField.apply_maximal
  {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {M : Type u} [Field M] [NumberField M] [Algebra K M]
-- given
  (h : IsHilbertClassField K L)
  (hfin : FiniteDimensional K M)
  (hgal : IsAbelianGalois K M)
  (hfinU : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal)
  (hinfU : IsUnramifiedAtInfinitePlaces K M) :
-- imply
  Nonempty (M →ₐ[K] L) :=
-- proof
  h.maximal M hfin hgal hfinU hinfU

end NumberField


-- created on 2026-10-20
-- updated on 2026-10-23
