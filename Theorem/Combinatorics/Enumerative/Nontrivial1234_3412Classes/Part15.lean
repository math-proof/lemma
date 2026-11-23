/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic
public import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part15

@[expose] public section

namespace MetaMathlibExt

lemma ntExists_perm_code {n : ℕ} {s : List ℕ}
    (hs : s ∈ List.permutations' (List.range n)) :
    ∃ σ : Equiv.Perm (Fin n), ntCode σ = s := by
  have hp : s.Perm (List.range n) := List.mem_permutations'.mp hs
  have hlen : s.length = n := by simpa using hp.length_eq
  have hnodup : s.Nodup := hp.nodup_iff.mpr List.nodup_range
  let idx : Fin n → Fin s.length := fun i => ⟨i.val, by rw [hlen]; exact i.is_lt⟩
  let f : Fin n → Fin n := fun i =>
    ⟨s.get (idx i), List.mem_range.mp (hp.mem_iff.mp (s.get_mem (idx i)))⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hget : s.get (idx i) = s.get (idx j) := congrArg Fin.val hij
    have hidx : idx i = idx j := hnodup.get_inj_iff.mp hget
    apply Fin.ext
    simpa only [idx] using congrArg Fin.val hidx
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_⟩
  apply List.ext_getElem
  · simpa [ntCode] using hlen.symm
  · intro i hiCode hiS
    have hi : i < n := by simpa [ntCode] using hiCode
    simp only [ntCode, List.getElem_ofFn]
    change (f ⟨i, hi⟩).val = s[i]
    rfl

end MetaMathlibExt
