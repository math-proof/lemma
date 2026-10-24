import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Idele
open scoped RestrictedProduct NumberField.AdeleRing
open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain
open NumberField
open FiniteIdeleGroup
open TopologicalIdeleGroup


namespace NumberField.TopologicalIdeleGroup

/--
[infinitePrincipalEmbedding_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
lemma infinitePrincipalEmbedding_apply
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ}
  {v : InfinitePlace K} :
-- imply
  infinitePrincipalEmbedding K x v =
    Units.map (algebraMap K v.Completion).toMonoidHom x :=
-- proof
  rfl

end NumberField.TopologicalIdeleGroup

namespace NumberField.TopologicalIdeleGroup

/--
[finitePrincipalEmbedding_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
lemma finitePrincipalEmbedding_apply
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ}
  {v : HeightOneSpectrum R} :
-- imply
  finitePrincipalEmbedding R K x v =
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x :=
-- proof
  rfl

end NumberField.TopologicalIdeleGroup

namespace NumberField.TopologicalIdeleGroup

/--
[principalEmbedding_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
lemma principalEmbedding_fst
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ} :
-- imply
  (principalEmbedding R K x).1 = infinitePrincipalEmbedding K x :=
-- proof
  rfl

end NumberField.TopologicalIdeleGroup

namespace NumberField.TopologicalIdeleGroup

/--
[principalEmbedding_snd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
lemma principalEmbedding_snd
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ} :
-- imply
  (principalEmbedding R K x).2 = finitePrincipalEmbedding R K x :=
-- proof
  rfl

end NumberField.TopologicalIdeleGroup

namespace NumberField.TopologicalIdeleGroup

/--
[unitsEquiv_globalUnit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
lemma unitsEquiv_globalUnit
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ} :
-- imply
  unitsEquiv R K (Units.map (algebraMap K (AdeleRing R K)).toMonoidHom x) =
    principalEmbedding R K x :=
-- proof
  rfl

end NumberField.TopologicalIdeleGroup

namespace NumberField.TopologicalIdeleGroup

/--
[principalEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
lemma principalEmbedding_injective
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [NumberField K] :
-- imply
  Function.Injective (principalEmbedding R K) := by
-- proof
  intro x y hxy
  have hmap :
    unitsEquiv R K (Units.map (algebraMap K (AdeleRing R K)).toMonoidHom x) =
      unitsEquiv R K (Units.map (algebraMap K (AdeleRing R K)).toMonoidHom y) := by
    simpa only [unitsEquiv_globalUnit] using hxy
  exact Units.map_injective (AdeleRing.algebraMap_injective R K) <|
    (unitsEquiv R K).injective hmap

end NumberField.TopologicalIdeleGroup

/--
[mem_localIntegralUnitSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
private lemma mem_localIntegralUnitSubgroup_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}
  {u : (v.adicCompletion K)ˣ} :
-- imply
  u ∈ localIntegralUnitSubgroup R K v ↔
    (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
    v.adicCompletionIntegers K := by
-- proof
  apply NumberField.mem_localIntegralUnitSubgroup R K

/--
[isOpen_localIntegralUnitSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
private lemma isOpen_localIntegralUnitSubgroup_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} :
-- imply
  IsOpen (localIntegralUnitSubgroup R K v : Set ((v.adicCompletion K)ˣ)) := by
-- proof
  apply NumberField.FiniteIdeleGroup.isOpen_localIntegralUnitSubgroup R K v


-- created on 2026-10-20
-- updated on 2026-10-23
