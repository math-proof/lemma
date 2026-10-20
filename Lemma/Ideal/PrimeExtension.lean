import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Ideal.PrimeExtension
open Ideal


/--
[isPrime_map_of_coprime_clearDenom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/PrimeExtension.lean)
-/
@[path]
private lemma isPrime_map_of_coprime_clearDenom_eq
  [CommRing O] [CommRing B] [Algebra O B]
  {p c : Ideal O}
-- given
  (hp : p.IsPrime)
  (hinj : Function.Injective (algebraMap O B))
  (hclear : ∀ x ∈ c, ∀ b : B, algebraMap O B x * b ∈ Set.range (algebraMap O B))
  (hsup : c ⊔ p = ⊤) :
-- imply
  (p.map (algebraMap O B)).IsPrime := by
-- proof
  apply Ideal.isPrime_map_of_coprime_clearDenom p c hp hinj hclear hsup

/--
[isMaximal_map_of_coprime_clearDenom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/PrimeExtension.lean)
-/
@[path]
private lemma isMaximal_map_of_coprime_clearDenom_eq
  [CommRing O] [CommRing B] [Algebra O B]
  {p c : Ideal O}
-- given
  (hp : p.IsMaximal)
  (hinj : Function.Injective (algebraMap O B))
  (hclear : ∀ x ∈ c, ∀ b : B, algebraMap O B x * b ∈ Set.range (algebraMap O B))
  (hsup : c ⊔ p = ⊤) :
-- imply
  (p.map (algebraMap O B)).IsMaximal := by
-- proof
  apply Ideal.isMaximal_map_of_coprime_clearDenom p c hp hinj hclear hsup

/--
[isMaximal_map_of_dimensionLEOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/PrimeExtension.lean)
-/
@[path]
private lemma isMaximal_map_of_dimensionLEOne_eq
  [CommRing O] [CommRing B] [Algebra O B] [Ring.DimensionLEOne O]
  {p c : Ideal O}
-- given
  (hp : p.IsPrime)
  (hne : p ≠ ⊥)
  (hinj : Function.Injective (algebraMap O B))
  (hclear : ∀ x ∈ c, ∀ b : B, algebraMap O B x * b ∈ Set.range (algebraMap O B))
  (hsup : c ⊔ p = ⊤) :
-- imply
  (p.map (algebraMap O B)).IsMaximal := by
-- proof
  apply Ideal.isMaximal_map_of_dimensionLEOne p c hp hne hinj hclear hsup


-- created on 2026-10-20
