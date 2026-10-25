/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Dynamics.PeriodicPts.Defs
import Lean.Elab.Tactic.Omega
import Def.Dynamics.Preperiodic


namespace Function

variable {α : Type*} {f : α → α} {x y z : α} {m n : ℕ}

theorem grandOrbitRel_refl (f : α → α) (x : α) : GrandOrbitRel f x x :=
  ⟨0, 0, rfl⟩

theorem GrandOrbitRel.symm (h : GrandOrbitRel f x y) : GrandOrbitRel f y x := by
  obtain ⟨m, n, heq⟩ := h
  exact ⟨n, m, heq.symm⟩

theorem GrandOrbitRel.trans (hxy : GrandOrbitRel f x y) (hyz : GrandOrbitRel f y z) :
    GrandOrbitRel f x z := by
  obtain ⟨m₁, n₁, hxy⟩ := hxy
  obtain ⟨m₂, n₂, hyz⟩ := hyz
  refine ⟨m₁ + m₂, n₁ + n₂, ?_⟩
  calc
    f^[m₁ + m₂] x = f^[m₂] (f^[m₁] x) := by
      rw [← iterate_add_apply]
      congr 1
      omega
    _ = f^[m₂] (f^[n₁] y) := congrArg _ hxy
    _ = f^[n₁] (f^[m₂] y) := by
      rw [← iterate_add_apply, ← iterate_add_apply]
      congr 1
      omega
    _ = f^[n₁] (f^[n₂] z) := congrArg _ hyz
    _ = f^[n₁ + n₂] z := (iterate_add_apply f n₁ n₂ z).symm

theorem grandOrbitRel_equivalence (f : α → α) : Equivalence (GrandOrbitRel f) where
  refl := grandOrbitRel_refl f
  symm := GrandOrbitRel.symm
  trans := GrandOrbitRel.trans

end Function
