module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Interval.Finset.Fin
public import Theorem.Combinatorics.SimpleGraph.Frucht.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

noncomputable def graphAutComapToFun {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) : ((Γ.comap ⇑f) ≃g (Γ.comap ⇑f)) → Γ ≃g Γ :=
  fun σ => RelIso.mk (f.permCongr σ.toEquiv)
    (fun {a b} => (graphAutComapForward_adj f Γ σ a b).symm)

noncomputable def graphAutComapInvFun {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) : (Γ ≃g Γ) → (Γ.comap ⇑f) ≃g (Γ.comap ⇑f) :=
  fun τ => RelIso.mk (f.symm.permCongr τ.toEquiv)
    (fun {a b} => (graphAutComapBackward_adj f Γ τ a b).symm)

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
