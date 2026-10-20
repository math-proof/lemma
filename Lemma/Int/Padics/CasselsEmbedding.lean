import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.CasselsEmbedding
open Subring


/--
[exists_injective_ringHom_closure_padicInt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/CasselsEmbedding.lean)
-/
@[path]
private lemma exists_injective_ringHom_closure_padicInt_eq
  [Field K] [CharZero K]
  {S : Finset K} :
-- imply
  ∃ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := by
-- proof
  apply Subring.exists_injective_ringHom_closure_padicInt S


-- created on 2026-10-20
