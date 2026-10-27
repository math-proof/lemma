import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.InformationTheory.HammingExpansion
open Hamming


namespace Hamming

/--
[mem_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
lemma mem_expansion
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {A : Finset (ι → F)}
  {x : ι → F}
  {t : ℕ} :
-- imply
  x ∈ expansion A t ↔ ∃ a ∈ A, hammingDist x a ≤ t := by
-- proof
  simp only [expansion, Finset.mem_biUnion, mem_ball, hammingDist_comm]

end Hamming

namespace Hamming

/--
[mem_expansion_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
lemma mem_expansion_of_mem
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {A : Finset (ι → F)}
  {x a : ι → F}
  {t : ℕ}
-- given
  (ha : a ∈ A)
  (h : hammingDist x a ≤ t) :
-- imply
  x ∈ expansion A t :=
-- proof
  mem_expansion.mpr ⟨a, ha, h⟩

end Hamming

namespace Hamming

/--
[expansion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
lemma expansion_empty
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {t : ℕ} :
-- imply
  expansion (∅ : Finset (ι → F)) t = ∅ := by
-- proof
  simp [expansion]

end Hamming

namespace Hamming

/--
[expansion_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
lemma expansion_singleton
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {a : ι → F}
  {t : ℕ} :
-- imply
  expansion {a} t = ball a t := by
-- proof
  simp [expansion]

end Hamming

namespace Hamming

/--
[subset_expansion_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
lemma subset_expansion_self
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {A : Finset (ι → F)}
  {t : ℕ} :
-- imply
  A ⊆ expansion A t := by
-- proof
  intro x hx
  rw [mem_expansion]
  exact ⟨x, hx, by simp [hammingDist_self]⟩

end Hamming

namespace Hamming

/--
[expansion_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
lemma expansion_mono
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {A B : Finset (ι → F)}
  {t : ℕ}
-- given
  (h : A ⊆ B) :
-- imply
  expansion A t ⊆ expansion B t := by
-- proof
  intro x hx
  rw [mem_expansion] at hx ⊢
  obtain ⟨a, ha, hdist⟩ := hx
  exact ⟨a, h ha, hdist⟩

end Hamming

namespace Hamming

/--
[isBall_ball](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean)
-/
@[path]
lemma isBall_ball
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {c : ι → F}
  {e : ℕ} :
-- imply
  IsBall (ball c e : Finset (ι → F)) :=
-- proof
  ⟨c, e, rfl⟩

end Hamming


-- created on 2026-10-20
-- updated on 2026-10-26
