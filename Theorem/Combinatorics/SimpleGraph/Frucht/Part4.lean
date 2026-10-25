/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Def.Combinatorics.SimpleGraph.Frucht.Part4


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

theorem graphAutComapForward_adj {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) (σ : (Γ.comap ⇑f) ≃g (Γ.comap ⇑f)) (a b : W1) :
    Γ.Adj a b ↔
      Γ.Adj ((f.permCongr σ.toEquiv) a) ((f.permCongr σ.toEquiv) b) := by
  have e1 : (Γ.comap ⇑f).Adj (f.symm a) (f.symm b) ↔ Γ.Adj a b := by
    rw [SimpleGraph.comap_adj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have e2 := (σ.map_adj_iff (v := f.symm a) (w := f.symm b)).symm
  have e3 : (Γ.comap ⇑f).Adj (σ (f.symm a)) (σ (f.symm b)) ↔
      Γ.Adj (f (σ (f.symm a))) (f (σ (f.symm b))) :=
    SimpleGraph.comap_adj
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply]
  calc Γ.Adj a b ↔ (Γ.comap ⇑f).Adj (f.symm a) (f.symm b) := e1.symm
    _ ↔ (Γ.comap ⇑f).Adj (σ (f.symm a)) (σ (f.symm b)) := e2
    _ ↔ Γ.Adj (f (σ (f.symm a))) (f (σ (f.symm b))) := e3

theorem graphAutComapBackward_adj {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) (τ : Γ ≃g Γ) (a b : V1) :
    (Γ.comap ⇑f).Adj a b ↔
      (Γ.comap ⇑f).Adj ((f.symm.permCongr τ.toEquiv) a)
        ((f.symm.permCongr τ.toEquiv) b) := by
  have e1 : (Γ.comap ⇑f).Adj a b ↔ Γ.Adj (f a) (f b) := SimpleGraph.comap_adj
  have e2 := (τ.map_adj_iff (v := f a) (w := f b)).symm
  have hperm : ∀ x : V1, (f.symm.permCongr τ.toEquiv) x = f.symm (τ (f x)) := by
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, RelIso.coe_fn_toEquiv]
  rw [hperm a, hperm b]
  have e3 : (Γ.comap ⇑f).Adj (f.symm (τ (f a))) (f.symm (τ (f b))) ↔
      Γ.Adj (τ (f a)) (τ (f b)) := by
    rw [SimpleGraph.comap_adj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  calc (Γ.comap ⇑f).Adj a b ↔ Γ.Adj (f a) (f b) := e1
    _ ↔ Γ.Adj (τ (f a)) (τ (f b)) := e2
    _ ↔ (Γ.comap ⇑f).Adj (f.symm (τ (f a))) (f.symm (τ (f b))) := e3.symm

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
