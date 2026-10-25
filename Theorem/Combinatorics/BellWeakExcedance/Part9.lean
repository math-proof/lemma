/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Def.Combinatorics.BellWeakExcedance.Part9


section

namespace MetaMathlibExt

theorem ofPartFun_mem_maxs {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {m : Fin n}
    (hm : m ∈ mins P) :
    ofPartFun P m ∈ maxs P := by
  unfold ofPartFun
  simp [hm]

theorem ofPartFun_eq_pred {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∉ mins P) : ofPartFun P u = pred P u hu := by
  unfold ofPartFun
  simp [hu]

theorem ofPartFun_eq_ofMem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∈ mins P) : ofPartFun P u =
      (maxs P).orderEmbOfFin (card_maxs_eq P)
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, hu⟩) := by
  unfold ofPartFun
  simp only [hu, dite_true]

theorem ofPartFun_injective {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Function.Injective (ofPartFun P) := by
  intro a b hab
  by_cases ha : a ∈ mins P <;> by_cases hb : b ∈ mins P
  · rw [ofPartFun_eq_ofMem ha, ofPartFun_eq_ofMem hb] at hab
    have hIdx := ((maxs P).orderEmbOfFin (card_maxs_eq P)).injective hab
    have hSub := ((mins P).orderIsoOfFin (card_mins_eq P)).symm.injective hIdx
    exact Subtype.ext_iff.mp hSub
  · have haX : ofPartFun P a ∈ maxs P := ofPartFun_mem_maxs ha
    have hbX : ofPartFun P b ∉ maxs P := by
      rw [ofPartFun_eq_pred hb]
      exact pred_not_mem_maxs hb
    rw [hab] at haX
    exact absurd haX hbX
  · have haX : ofPartFun P a ∉ maxs P := by
      rw [ofPartFun_eq_pred ha]
      exact pred_not_mem_maxs ha
    have hbX : ofPartFun P b ∈ maxs P := ofPartFun_mem_maxs hb
    rw [← hab] at hbX
    exact absurd hbX haX
  · rw [ofPartFun_eq_pred ha, ofPartFun_eq_pred hb] at hab
    exact pred_injective hab

end MetaMathlibExt
end
