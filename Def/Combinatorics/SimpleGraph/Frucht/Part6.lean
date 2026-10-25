/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Combinatorics.SimpleGraph.Frucht.Part5


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

noncomputable def graphAutComapEquiv {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) : ((Γ.comap ⇑f) ≃g (Γ.comap ⇑f)) ≃* (Γ ≃g Γ) where
  toFun := graphAutComapToFun f Γ
  invFun := graphAutComapInvFun f Γ
  left_inv := by
    intro σ
    apply RelIso.ext
    intro x
    have h := congrArg (fun p : Equiv.Perm V1 => p x)
      (permCongr_roundtrip_left f σ.toEquiv)
    exact h
  right_inv := by
    intro τ
    apply RelIso.ext
    intro x
    have h := congrArg (fun p : Equiv.Perm W1 => p x)
      (permCongr_roundtrip_right f τ.toEquiv)
    exact h
  map_mul' := by
    intro a b
    apply RelIso.ext
    intro x
    have htrans : (a * b).toEquiv = a.toEquiv * b.toEquiv := by
      apply Equiv.ext
      intro y
      rfl
    show (f.permCongr (a * b).toEquiv) x = _
    rw [htrans, Equiv.permCongr_mul, Equiv.Perm.mul_apply]
    rfl

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
