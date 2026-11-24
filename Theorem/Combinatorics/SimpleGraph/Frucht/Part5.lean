module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Interval.Finset.Fin
public import Def.Combinatorics.SimpleGraph.Frucht.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

theorem permCongr_roundtrip_left {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (p : Equiv.Perm V1) :
    f.symm.permCongr (f.permCongr p) = p := by
  apply Equiv.ext
  intro x
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem permCongr_roundtrip_right {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (q : Equiv.Perm W1) :
    f.permCongr (f.symm.permCongr q) = q := by
  apply Equiv.ext
  intro x
  simp only [Equiv.permCongr_apply, Equiv.apply_symm_apply, Equiv.symm_symm]

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
