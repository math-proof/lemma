import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed.lean)
-/
@[path]
private lemma main
  {X : Scheme.{u}}
  {S : Set X}
  {x : X}
-- given
  (hS : S.Finite)
  (hcl : ∀ s ∈ S, IsClosed ({s} : Set X))
  (hx : x ∉ S) :
-- imply
  ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Disjoint (V : Set X) S := by
-- proof
  classical
  have hSc : IsClosed S := by
    have h : S = ⋃ s ∈ S, ({s} : Set X) := (Set.biUnion_of_singleton S).symm
    rw [h]
    exact hS.isClosed_biUnion fun s hs => hcl s hs
  let U : X.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hxU : x ∈ U := hx
  obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxU
  exact ⟨V, hV, hxV, Set.disjoint_left.mpr fun z hz hzS => (hVU hz) hzS⟩


-- created on 2026-10-05
