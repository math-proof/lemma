import Mathlib
import sympy.Basic

open Module

/--
[Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf.lean)
-/
@[main]
private lemma main
  [Field k]
  {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {f : V →ₗ[k] W}
  {N : Submodule k W} [FiniteDimensional k (N.comap f)] :
-- imply
  finrank k (N.comap f)
      = finrank k (LinearMap.ker f) + finrank k (LinearMap.range f ⊓ N : Submodule k W) := by
-- proof
  have hker : LinearMap.ker f ≤ N.comap f := fun x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker.mp hx, Submodule.zero_mem]
  have h := LinearMap.finrank_range_add_finrank_ker (f ∘ₗ (N.comap f).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_eq,
    LinearMap.ker_comp, (Submodule.comapSubtypeEquivOfLe hker).finrank_eq] at h
  omega


-- created on 2026-10-05
