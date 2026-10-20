import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Idele
open scoped RestrictedProduct NumberField.AdeleRing
open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain
open NumberField
open FiniteIdeleGroup
open TopologicalIdeleGroup


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

/--
[infinitePrincipalEmbedding_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
private lemma infinitePrincipalEmbedding_apply_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ}
  {v : InfinitePlace K} :
-- imply
  infinitePrincipalEmbedding K x v =
    Units.map (algebraMap K v.Completion).toMonoidHom x := by
-- proof
  apply NumberField.TopologicalIdeleGroup.infinitePrincipalEmbedding_apply R K x v

/--
[finitePrincipalEmbedding_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
private lemma finitePrincipalEmbedding_apply_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ}
  {v : HeightOneSpectrum R} :
-- imply
  finitePrincipalEmbedding R K x v =
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x := by
-- proof
  apply NumberField.TopologicalIdeleGroup.finitePrincipalEmbedding_apply R K x v

/--
[principalEmbedding_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
private lemma principalEmbedding_fst_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ} :
-- imply
  (principalEmbedding R K x).1 = infinitePrincipalEmbedding K x := by
-- proof
  apply NumberField.TopologicalIdeleGroup.principalEmbedding_fst R K x

/--
[principalEmbedding_snd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
private lemma principalEmbedding_snd_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ} :
-- imply
  (principalEmbedding R K x).2 = finitePrincipalEmbedding R K x := by
-- proof
  apply NumberField.TopologicalIdeleGroup.principalEmbedding_snd R K x

/--
[unitsEquiv_globalUnit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
private lemma unitsEquiv_globalUnit_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {x : Kˣ} :
-- imply
  unitsEquiv R K (Units.map (algebraMap K (AdeleRing R K)).toMonoidHom x) =
    principalEmbedding R K x := by
-- proof
  apply NumberField.TopologicalIdeleGroup.unitsEquiv_globalUnit R K x

/--
[principalEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean)
-/
@[path]
private lemma principalEmbedding_injective_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [NumberField K] :
-- imply
  Function.Injective (principalEmbedding R K) := by
-- proof
  apply NumberField.TopologicalIdeleGroup.principalEmbedding_injective R K


-- created on 2026-10-20
