/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/HilbertClassField.lean -/


import Structure.NumberTheory.NumberField.HilbertClassField
import Lemma.Nat.NumberField.HilbertClassField
open scoped NumberField

universe u


-- Construct the predicate from all five components.
example {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    (hfin : FiniteDimensional K L)
    (hgal : IsAbelianGalois K L)
    (hfinU : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal)
    (hinfU : IsUnramifiedAtInfinitePlaces K L)
    (hmax : ∀ (M : Type u) [Field M] [NumberField M] [Algebra K M],
      FiniteDimensional K M →
      IsAbelianGalois K M →
      (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal) →
      IsUnramifiedAtInfinitePlaces K M →
      Nonempty (M →ₐ[K] L)) :
    NumberField.IsHilbertClassField K L :=
  NumberField.IsHilbertClassField.mk hfin hgal hfinU hinfU hmax

-- Project finite-prime unramifiedness at a given height-one prime.
example {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (h : NumberField.IsHilbertClassField K L)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal :=
  h.isUnramified_finite 𝔭

-- Project infinite-place unramifiedness.
example {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (h : NumberField.IsHilbertClassField K L) :
    IsUnramifiedAtInfinitePlaces K L :=
  h.isUnramified_infinite

-- Invoke maximality directly to obtain a `K`-algebra embedding.
example {K L M : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [Field M] [NumberField M] [Algebra K M]
    (h : NumberField.IsHilbertClassField K L)
    (hfin : FiniteDimensional K M)
    (hgal : IsAbelianGalois K M)
    (hfinU : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal)
    (hinfU : IsUnramifiedAtInfinitePlaces K M) :
    Nonempty (M →ₐ[K] L) :=
  h.maximal M hfin hgal hfinU hinfU

-- The `NumberField` hypotheses are explicit parameters of the predicate:
-- the constructor takes all five instances.
example {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    (hfin : FiniteDimensional K L)
    (hgal : IsAbelianGalois K L)
    (hfinU : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal)
    (hinfU : IsUnramifiedAtInfinitePlaces K L)
    (hmax : ∀ (M : Type u) [Field M] [NumberField M] [Algebra K M],
      FiniteDimensional K M →
      IsAbelianGalois K M →
      (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal) →
      IsUnramifiedAtInfinitePlaces K M →
      Nonempty (M →ₐ[K] L)) :
    NumberField.IsHilbertClassField K L :=
  @NumberField.IsHilbertClassField.mk K L _ _ _ _ _ hfin hgal hfinU hinfU hmax

-- Invoke maximality through the application lemma.
example {K L M : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [Field M] [NumberField M] [Algebra K M]
    (h : NumberField.IsHilbertClassField K L)
    (hfin : FiniteDimensional K M)
    (hgal : IsAbelianGalois K M)
    (hfinU : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal)
    (hinfU : IsUnramifiedAtInfinitePlaces K M) :
    Nonempty (M →ₐ[K] L) :=
  h.apply_maximal hfin hgal hfinU hinfU

