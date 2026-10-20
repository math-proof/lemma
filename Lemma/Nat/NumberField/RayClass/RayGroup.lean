import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.RayGroup
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[mem_coprimeFractionalIdeals_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma mem_coprimeFractionalIdeals_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
-- imply
  u ∈ coprimeFractionalIdeals m ↔
    ∀ v, finiteSupported m v →
    FractionalIdeal.count K v (u : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
-- proof
  apply NumberField.Modulus.mem_coprimeFractionalIdeals_iff m u

/--
[mem_rayElements_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma mem_rayElements_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ} :
-- imply
  x ∈ rayElements m ↔
    toPrincipalIdeal (𝓞 K) K x ∈
    coprimeFractionalIdeals m := by
-- proof
  apply NumberField.Modulus.mem_rayElements_iff m x

/--
[IsRayElementOne.mem_rayElements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma IsRayElementOne_mem_rayElements_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (h : IsRayElementOne m x) :
-- imply
  x ∈ rayElements m := by
-- proof
  apply NumberField.Modulus.IsRayElementOne.mem_rayElements h

/--
[IsRayElementOne.congruent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma IsRayElementOne_congruent_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (h : IsRayElementOne m x) :
-- imply
  CongruentOneAtFinitePart m x := by
-- proof
  apply NumberField.Modulus.IsRayElementOne.congruent h

/--
[IsRayElementOne.positive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma IsRayElementOne_positive_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (h : IsRayElementOne m x) :
-- imply
  PositiveAtInfinitePart m x := by
-- proof
  apply NumberField.Modulus.IsRayElementOne.positive h

/--
[rayGenerators_mem_of_isRayElementOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma rayGenerators_mem_of_isRayElementOne_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (hx : IsRayElementOne m x) :
-- imply
  (⟨toPrincipalIdeal (𝓞 K) K x,
    Subgroup.mem_comap.mp hx.1⟩ :
    coprimeFractionalIdeals m) ∈ rayGenerators m := by
-- proof
  apply NumberField.Modulus.rayGenerators_mem_of_isRayElementOne m x hx

/--
[mem_rayGroup_of_isRayElementOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma mem_rayGroup_of_isRayElementOne_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (hx : IsRayElementOne m x) :
-- imply
  (⟨toPrincipalIdeal (𝓞 K) K x,
    Subgroup.mem_comap.mp hx.1⟩ :
    coprimeFractionalIdeals m) ∈ rayGroup m := by
-- proof
  apply NumberField.Modulus.mem_rayGroup_of_isRayElementOne m x hx

/--
[rayGroup_closure_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma rayGroup_closure_le_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {H : Subgroup (coprimeFractionalIdeals m)}
-- given
  (h : rayGenerators m ⊆ (↑H : Set _)) :
-- imply
  rayGroup m ≤ H := by
-- proof
  apply NumberField.Modulus.rayGroup_closure_le h

/--
[congruentOneAtFinitePart_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma congruentOneAtFinitePart_one_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  CongruentOneAtFinitePart m 1 := by
-- proof
  apply NumberField.Modulus.congruentOneAtFinitePart_one m

/--
[positiveAtInfinitePart_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma positiveAtInfinitePart_one_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  PositiveAtInfinitePart m 1 := by
-- proof
  apply NumberField.Modulus.positiveAtInfinitePart_one m

/--
[isRayElementOne_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
private lemma isRayElementOne_one_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  IsRayElementOne m 1 := by
-- proof
  apply NumberField.Modulus.isRayElementOne_one m


-- created on 2026-10-20
