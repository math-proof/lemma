import Mathlib
import sympy.Basic
import sympy.series.NormalConvergence

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma sup_norm_on_empty_eq
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  (g : X → E) :
-- imply
  supNormOn g ∅ = 0 := by
-- proof
  apply supNormOn_empty g

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma sup_norm_on_zero_eq
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  (S : Set X) :
-- imply
  supNormOn (0 : X → E) S = 0 := by
-- proof
  apply supNormOn_zero S

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma sup_norm_on_mono_le
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  {S T : Set X}
  (h : T ⊆ S)
  (g : X → E) :
-- imply
  supNormOn g T ≤ supNormOn g S := by
-- proof
  apply supNormOn_mono h g

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma converges_normally_on_empty_is
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  (f : ℕ → X → E) :
-- imply
  ConvergesNormallyOn f ∅ := by
-- proof
  apply convergesNormallyOn_empty f

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma converges_normally_on_zero_is
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  (S : Set X) :
-- imply
  ConvergesNormallyOn (0 : ℕ → X → E) S := by
-- proof
  apply convergesNormallyOn_zero S

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma converges_normally_on_mono_is
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  {f : ℕ → X → E} {S T : Set X}
  (h : ConvergesNormallyOn f S)
  (hTS : T ⊆ S) :
-- imply
  ConvergesNormallyOn f T := by
-- proof
  apply ConvergesNormallyOn.mono h hTS

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma converges_locally_normally_on_exists_nhds_inter_is
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]
  {f : ℕ → X → E} {S : Set X} {x : X}
  (h : ConvergesLocallyNormallyOn f S)
  (hx : x ∈ S) :
-- imply
  ∃ U ∈ nhds x, ConvergesNormallyOn f (U ∩ S) := by
-- proof
  apply ConvergesLocallyNormallyOn.exists_nhds_inter h hx

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma converges_locally_normally_on_empty_is
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]
  (f : ℕ → X → E) :
-- imply
  ConvergesLocallyNormallyOn f ∅ := by
-- proof
  apply convergesLocallyNormallyOn_empty f

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma converges_locally_normally_on_zero_is
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]
  (S : Set X) :
-- imply
  ConvergesLocallyNormallyOn (0 : ℕ → X → E) S := by
-- proof
  apply convergesLocallyNormallyOn_zero S

/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
private lemma converges_locally_normally_on_mono_is
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]
  {f : ℕ → X → E} {S T : Set X}
  (h : ConvergesLocallyNormallyOn f S)
  (hTS : T ⊆ S) :
-- imply
  ConvergesLocallyNormallyOn f T := by
-- proof
  apply ConvergesLocallyNormallyOn.mono h hTS

-- created on 2026-10-10
