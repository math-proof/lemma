import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Stirling
open MetaMathlibExt


/--
[cycleQuotientCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma cycleQuotientCount_eq_eq
  [Fintype α] [DecidableEq α]
  {σ : Equiv.Perm α} :
-- imply
  cycleQuotientCount σ =
    Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) := by
-- proof
  apply MetaMathlibExt.cycleQuotientCount_eq σ

/--
[card_perm_cycleCount_eq_stirlingFirst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma card_perm_cycleCount_eq_stirlingFirst_eq
  {n k : ℕ} :
-- imply
  Fintype.card {σ : Equiv.Perm (Fin n) //
    Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = k} =
    Nat.stirlingFirst n k := by
-- proof
  apply MetaMathlibExt.card_perm_cycleCount_eq_stirlingFirst n k


-- created on 2026-10-20
