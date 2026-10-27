import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.InformationTheory.PrefixFree
open MathlibExt.InformationTheory


namespace MathlibExt.InformationTheory

/--
[IsPrefixFree.eq_of_isPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/PrefixFree.lean)
-/
@[path]
lemma IsPrefixFree.eq_of_isPrefix
  {code : α → List β}
  {a₁ a₂ : α}
-- given
  (h : IsPrefixFree code)
  (hpre : code a₁ <+: code a₂) :
-- imply
  a₁ = a₂ := by
-- proof
  by_contra hne
  exact h hne hpre

end MathlibExt.InformationTheory

namespace MathlibExt.InformationTheory

/--
[IsPrefixFree.injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/PrefixFree.lean)
-/
@[path]
lemma IsPrefixFree.injective
  {code : α → List β}
-- given
  (h : IsPrefixFree code) :
-- imply
  Function.Injective code := by
-- proof
  intro a₁ a₂ heq
  by_contra hne
  exact h hne ⟨[], by simp [heq]⟩

end MathlibExt.InformationTheory

namespace MathlibExt.InformationTheory

/--
[IsPrefixFree.eq_of_mem_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/PrefixFree.lean)
-/
@[path]
lemma IsPrefixFree.eq_of_mem_nil
  {code : α → List β}
  {a₀ a : α}
-- given
  (h : IsPrefixFree code)
  (ha₀ : code a₀ = []) :
-- imply
  a = a₀ := by
-- proof
  by_contra hne
  apply h (fun heq => hne heq.symm) _
  rw [ha₀]
  exact ⟨_, rfl⟩

end MathlibExt.InformationTheory


-- created on 2026-10-20
-- updated on 2026-10-26
