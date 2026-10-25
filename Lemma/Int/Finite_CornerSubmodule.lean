import Mathlib
import sympy.Basic
import Lemma.IharaLemma.IdempotentSplitting


/--
[IharaLemma_finite_cornerSubmodule](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_finite_cornerSubmodule.lean)
-/
@[path]
private lemma main
  [CommRing 𝒪] [CommRing B] [Algebra 𝒪 B] [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V] [Module.Finite 𝒪 V]
  {e : B} :
-- imply
  Module.Finite 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e) := by
-- proof
  have h : (IharaLemma.cornerSubmodule (M := V) e).restrictScalars 𝒪 = LinearMap.range ((e • (LinearMap.id : V →ₗ[B] V)).restrictScalars 𝒪) := by
    ext v
    simp only [Submodule.restrictScalars_mem, IharaLemma.cornerSubmodule, LinearMap.mem_range, LinearMap.coe_restrictScalars]
  rw [show (Module.Finite 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e)) = Module.Finite 𝒪 ↥((IharaLemma.cornerSubmodule (M := V) e).restrictScalars 𝒪) from rfl, h]
  exact Module.Finite.range _


-- created on 2026-10-24
