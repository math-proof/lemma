/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fintype.Fin
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part11


section

namespace MetaMathlibExt

theorem wmiUnpack_pack {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) :
    wmiUnpack k (wmiPackSym k S) = S := by
  funext i
  apply Sym.ext
  change ((wmiPack k S).filter (fun q => (ofLex q).2 = i)).map
    (fun q => (ofLex q).1) = (S i).val
  rw [wmiPack_filter, Multiset.map_map]
  simp [Function.comp_def]

theorem wmiPack_unpack_piece {m x : ℕ} (k : Fin m → ℕ)
    (M : wmiPairSymData m (∑ i, k i) x k) (i : Fin m) :
    ((wmiUnpack k M i).val.map (fun v => toLex (v, i))) =
      M.1.val.filter (fun q => (ofLex q).2 = i) := by
  change ((M.1.val.filter (fun q => (ofLex q).2 = i)).map
    (fun q => (ofLex q).1)).map (fun v => toLex (v, i)) = _
  rw [Multiset.map_map]
  calc
    _ = (M.1.val.filter (fun q => (ofLex q).2 = i)).map id := by
      apply Multiset.map_congr rfl
      intro q hq
      have hi : (ofLex q).2 = i := (Multiset.mem_filter.mp hq).2
      change toLex ((ofLex q).1, i) = q
      have hp : ((ofLex q).1, i) = ofLex q := Prod.ext rfl hi.symm
      rw [hp]
      exact toLex.apply_symm_apply q
    _ = _ := Multiset.map_id _

theorem wmiPack_unpack {m x : ℕ} (k : Fin m → ℕ)
    (M : wmiPairSymData m (∑ i, k i) x k) :
    wmiPackSym k (wmiUnpack k M) = M := by
  apply Subtype.ext
  apply Sym.ext
  change wmiPack k (wmiUnpack k M) = M.1.val
  unfold wmiPack
  calc
    (∑ i, (wmiUnpack k M i).val.map (fun v => toLex (v, i))) =
        ∑ i, M.1.val.filter (fun q => (ofLex q).2 = i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact wmiPack_unpack_piece k M i
    _ = M.1.val := wmi_sum_filter_fibers M.1.val (fun q => (ofLex q).2)

end MetaMathlibExt
end
