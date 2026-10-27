import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
open scoped nonZeroDivisors
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[IsRayElementOne.mem_rayElements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
lemma IsRayElementOne.mem_rayElements
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (h : IsRayElementOne m x) :
-- imply
  x ∈ rayElements m :=
-- proof
  h.1

end NumberField.Modulus

namespace NumberField.Modulus

/--
[IsRayElementOne.congruent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
lemma IsRayElementOne.congruent
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (h : IsRayElementOne m x) :
-- imply
  CongruentOneAtFinitePart m x :=
-- proof
  h.2.1

end NumberField.Modulus

namespace NumberField.Modulus

/--
[IsRayElementOne.positive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
lemma IsRayElementOne.positive
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (h : IsRayElementOne m x) :
-- imply
  PositiveAtInfinitePart m x :=
-- proof
  h.2.2

end NumberField.Modulus

namespace NumberField.Modulus

/--
[positiveAtInfinitePart_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
lemma positiveAtInfinitePart_one
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  PositiveAtInfinitePart m 1 := by
-- proof
  intro w _
  rwa [Units.val_one, map_one]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[isRayElementOne_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean)
-/
@[path]
lemma isRayElementOne_one
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  IsRayElementOne m 1 :=
-- proof
  ⟨one_mem _, congruentOneAtFinitePart_one m, positiveAtInfinitePart_one m⟩

end NumberField.Modulus

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


-- created on 2026-10-20
-- updated on 2026-10-26
