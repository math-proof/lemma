import Mathlib
import sympy.Basic
import sympy.series.NormalConvergence
open Topology
open scoped ENNReal


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma eq_zero_of_supNormOn_empty
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  (g : X → E) :
-- imply
  supNormOn g ∅ = 0 := by
-- proof
  unfold supNormOn
  rw [iSup_of_empty]
  rfl


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma eq_zero_of_supNormOn_zero
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  (S : Set X) :
-- imply
  supNormOn (0 : X → E) S = 0 := by
-- proof
  simp [supNormOn]


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma le_supNormOn_of_subset
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  {S T : Set X}
  (h : T ⊆ S)
  (g : X → E) :
-- imply
  supNormOn g T ≤ supNormOn g S := by
-- proof
  unfold supNormOn
  apply iSup_mono'
  intro x
  exact ⟨⟨x.1, h x.2⟩, le_rfl⟩


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma convergesNormallyOn_of_empty
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  (f : ℕ → X → E) :
-- imply
  ConvergesNormallyOn f ∅ := by
-- proof
  simp [ConvergesNormallyOn, eq_zero_of_supNormOn_empty]


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma convergesNormallyOn_of_zero
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  (S : Set X) :
-- imply
  ConvergesNormallyOn (0 : ℕ → X → E) S := by
-- proof
  simp [ConvergesNormallyOn, eq_zero_of_supNormOn_zero]


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma convergesLocallyNormallyOn_of_empty
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]
  (f : ℕ → X → E) :
-- imply
  ConvergesLocallyNormallyOn f ∅ :=
-- proof
  fun x hx => absurd hx (Set.notMem_empty x)


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma convergesLocallyNormallyOn_of_zero
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]
  (S : Set X) :
-- imply
  ConvergesLocallyNormallyOn (0 : ℕ → X → E) S := by
-- proof
  intro x _
  exact ⟨Set.univ, Filter.univ_mem, by simp⟩


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma ConvergesNormallyOn.of_subset
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*}
  {f : ℕ → X → E} {S T : Set X}
  (h : ConvergesNormallyOn f S)
  (hTS : T ⊆ S) :
-- imply
  ConvergesNormallyOn f T := by
-- proof
  unfold ConvergesNormallyOn at h ⊢
  exact ne_top_of_le_ne_top h (ENNReal.tsum_le_tsum fun n => le_supNormOn_of_subset hTS _)


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma ConvergesLocallyNormallyOn.exists_nhds_inter'
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]
  {f : ℕ → X → E} {S : Set X} {x : X}
  (h : ConvergesLocallyNormallyOn f S)
  (hx : x ∈ S) :
-- imply
  ∃ U ∈ nhds x, ConvergesNormallyOn f (U ∩ S) :=
-- proof
  h x hx


/--
[NormalConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma ConvergesLocallyNormallyOn.of_subset
-- given
  {E : Type*} [SeminormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]
  {f : ℕ → X → E} {S T : Set X}
  (h : ConvergesLocallyNormallyOn f S)
  (hTS : T ⊆ S) :
-- imply
  ConvergesLocallyNormallyOn f T := by
-- proof
  intro x hx
  obtain ⟨U, hU, hconv⟩ := h x (hTS hx)
  exact ⟨U, hU, ConvergesNormallyOn.of_subset hconv (Set.inter_subset_inter (fun _ hx => hx) hTS)⟩


-- created on 2026-10-10
-- updated on 2026-10-24
