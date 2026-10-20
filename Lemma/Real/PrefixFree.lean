import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.PrefixFree
open MathlibExt.InformationTheory


/--
[IsPrefixFree.eq_of_isPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/PrefixFree.lean)
-/
@[path]
private lemma IsPrefixFree_eq_of_isPrefix_eq
  {code : α → List β}
  {a₁ a₂ : α}
-- given
  (h : IsPrefixFree code)
  (hpre : code a₁ <+: code a₂) :
-- imply
  a₁ = a₂ := by
-- proof
  apply MathlibExt.InformationTheory.IsPrefixFree.eq_of_isPrefix h hpre

/--
[IsPrefixFree.injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/PrefixFree.lean)
-/
@[path]
private lemma IsPrefixFree_injective_eq
  {code : α → List β}
-- given
  (h : IsPrefixFree code) :
-- imply
  Function.Injective code := by
-- proof
  apply MathlibExt.InformationTheory.IsPrefixFree.injective h

/--
[IsPrefixFree.eq_of_mem_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/PrefixFree.lean)
-/
@[path]
private lemma IsPrefixFree_eq_of_mem_nil_eq
  {code : α → List β}
  {a₀ : α}
  {a : α}
-- given
  (h : IsPrefixFree code)
  (ha₀ : code a₀ = []) :
-- imply
  a = a₀ := by
-- proof
  apply MathlibExt.InformationTheory.IsPrefixFree.eq_of_mem_nil h ha₀ a


-- created on 2026-10-20
