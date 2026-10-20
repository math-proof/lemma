import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.IdeleNorm
open NumberField.TopologicalIdeleGroup


/--
[adelicNorm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean)
-/
@[path]
private lemma adelicNorm_apply_eq
  [Field K] [NumberField K]
  {a : TopologicalIdeleGroup (𝓞 K) K} :
-- imply
  adelicNorm K a =
    (∏ w : InfinitePlace K, ‖(a.1 w : w.Completion)‖ ^ w.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ‖(a.2 v : v.adicCompletion K)‖ := by
-- proof
  apply NumberField.TopologicalIdeleGroup.adelicNorm_apply K a

/--
[mem_normOneIdeles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean)
-/
@[path]
private lemma mem_normOneIdeles_eq
  [Field K] [NumberField K]
  {a : TopologicalIdeleGroup (𝓞 K) K} :
-- imply
  a ∈ normOneIdeles K ↔ adelicNorm K a = 1 := by
-- proof
  apply NumberField.TopologicalIdeleGroup.mem_normOneIdeles K

/--
[adelicNorm_principalEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean)
-/
@[path]
private lemma adelicNorm_principalEmbedding_eq
  [Field K] [NumberField K]
  {x : Kˣ} :
-- imply
  adelicNorm K (principalEmbedding (𝓞 K) K x) = 1 := by
-- proof
  apply NumberField.TopologicalIdeleGroup.adelicNorm_principalEmbedding K x

/--
[principalIdeles_le_normOneIdeles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean)
-/
@[path]
private lemma principalIdeles_le_normOneIdeles_eq
  [Field K] [NumberField K] :
-- imply
  principalIdeles (𝓞 K) K ≤ normOneIdeles K := by
-- proof
  apply NumberField.TopologicalIdeleGroup.principalIdeles_le_normOneIdeles K


-- created on 2026-10-20
