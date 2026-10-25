/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Abbrev.Combinatorics.BellPermutationsSecondKind


namespace MetaMathlibExt

def E1 (n K : ℕ) : Asub (n+1) K ≃ Psub n K where
  toFun f := ⟨(restr f.1 f.2.1, f.1 (Fin.last n)),
    ⟨restr_rgf f.1 f.2.1, last_le f.1 f.2.1, by rw [← decomp f.1 f.2.1]; exact f.2.2⟩⟩
  invFun p := ⟨ext p.1.1 p.1.2, ⟨ext_rgf p.2.1 p.1.2 p.2.2.1, p.2.2.2⟩⟩
  left_inv f := by
    apply Subtype.ext
    exact (decomp f.1 f.2.1).symm
  right_inv p := by
    obtain ⟨⟨g, v⟩, hp⟩ := p
    apply Subtype.ext
    change (restr (ext g v) (ext_rgf hp.1 v hp.2.1), ext g v (Fin.last n)) = (g, v)
    rw [restr_ext, ext_last]

def extPair_inl {n k : ℕ} (g : Asub n (k + 1)) (i : Fin (k + 1)) : Psub n (k+1) := by
  have hb : i.val < n + 1 := by
    have := numVals_le g.1; have := g.2.2; have := i.isLt; omega
  have hlt : (⟨i.val, hb⟩ : Fin (n+1)).val < numVals g.1 := by
    change i.val < numVals g.1; have := g.2.2; have := i.isLt; omega
  exact ⟨(g.1, ⟨i.val, hb⟩), g.2.1, le_of_lt hlt, by rw [numVals_ext_lt g.2.1 _ hlt, g.2.2]⟩

def extPair_inr {n k : ℕ} (g : Asub n k) : Psub n (k+1) := by
  have hb : numVals g.1 < n + 1 := by have := numVals_le g.1; omega
  have heq : (⟨numVals g.1, hb⟩ : Fin (n+1)).val = numVals g.1 := rfl
  exact ⟨(g.1, ⟨numVals g.1, hb⟩), g.2.1, le_of_eq heq, by rw [numVals_ext_eq g.2.1 _ heq, g.2.2]⟩

def fromSum (n k : ℕ) : ((Asub n (k+1)) × Fin (k+1)) ⊕ Asub n k → Psub n (k+1)
  | Sum.inl (g, i) => extPair_inl g i
  | Sum.inr g => extPair_inr g

end MetaMathlibExt
