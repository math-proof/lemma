import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.HammingExpansion
open Hamming


/--
[mem_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
private lemma mem_expansion_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {A : Finset (ι → F)}
  {x : ι → F}
  {t : ℕ} :
-- imply
  x ∈ expansion A t ↔ ∃ a ∈ A, hammingDist x a ≤ t := by
-- proof
  apply Hamming.mem_expansion

/--
[mem_expansion_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
private lemma mem_expansion_of_mem_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {A : Finset (ι → F)}
  {x a : ι → F}
  {t : ℕ}
-- given
  (ha : a ∈ A)
  (h : hammingDist x a ≤ t) :
-- imply
  x ∈ expansion A t := by
-- proof
  apply Hamming.mem_expansion_of_mem ha h

/--
[expansion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
private lemma expansion_empty_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {t : ℕ} :
-- imply
  expansion (∅ : Finset (ι → F)) t = ∅ := by
-- proof
  apply Hamming.expansion_empty t

/--
[expansion_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
private lemma expansion_singleton_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {a : ι → F}
  {t : ℕ} :
-- imply
  expansion {a} t = ball a t := by
-- proof
  apply Hamming.expansion_singleton a t

/--
[subset_expansion_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
private lemma subset_expansion_self_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {A : Finset (ι → F)}
  {t : ℕ} :
-- imply
  A ⊆ expansion A t := by
-- proof
  apply Hamming.subset_expansion_self A t

/--
[expansion_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
private lemma expansion_mono_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {A B : Finset (ι → F)}
  {t : ℕ}
-- given
  (h : A ⊆ B) :
-- imply
  expansion A t ⊆ expansion B t := by
-- proof
  apply Hamming.expansion_mono h

/--
[isBall_ball](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
private lemma isBall_ball_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {c : ι → F}
  {e : ℕ} :
-- imply
  IsBall (ball c e : Finset (ι → F)) := by
-- proof
  apply Hamming.isBall_ball c e


-- created on 2026-10-20
