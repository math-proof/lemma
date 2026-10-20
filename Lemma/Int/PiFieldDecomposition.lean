import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PiFieldDecomposition
open PiFieldQuotient


/--
[exists_indexEquiv_algEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldDecomposition.lean)
-/
@[path]
private lemma exists_indexEquiv_algEquiv_eq
  {K : Type u} [Field K]
  {ι : Type v} [Finite ι]
  {κ : Type w} [Finite κ]
  {F : ι → Type x} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {G : κ → Type y} [∀ j, Field (G j)] [∀ j, Algebra K (G j)]
-- given
  (e : (∀ i, F i) ≃ₐ[K] (∀ j, G j)) :
-- imply
  ∃ σ : ι ≃ κ, ∀ i, Nonempty (F i ≃ₐ[K] G (σ i)) := by
-- proof
  apply PiFieldQuotient.exists_indexEquiv_algEquiv e


-- created on 2026-10-20
