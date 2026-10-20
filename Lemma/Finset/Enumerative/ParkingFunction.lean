import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.ParkingFunction
open MetaMathlibExt


/--
[isParkingFunction_iff_card_filter_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ParkingFunction.lean)
-/
@[path]
private lemma isParkingFunction_iff_card_filter_le_eq
  {n : ℕ}
  {f : Fin n → Fin n} :
-- imply
  IsParkingFunction n f ↔
    ∀ k : Fin n,
    k.val + 1 ≤ (Finset.univ.filter (fun i : Fin n ↦ f i ≤ k)).card := by
-- proof
  apply MetaMathlibExt.isParkingFunction_iff_card_filter_le n f


-- created on 2026-10-20
