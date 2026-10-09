import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry TopologicalSpace

/--
[AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap.lean)
-/
@[path]
private lemma main
  {X S : Scheme.{u}} [JacobsonSpace ↑X]
  {f : X ⟶ S} [LocallyOfFinitePresentation f]
-- given
  (h : ∀ x : ↑X, IsClosed ({x} : Set ↑X) → (f.stalkMap x).hom.FormallySmooth) :
-- imply
  Smooth f := by
-- proof
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  by_contra hne
  have hne' : ((f.smoothLocus : Set ↑X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro htop
    exact hne (TopologicalSpace.Opens.ext htop)
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne' (f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed)
  exact hx ((Scheme.Hom.mem_smoothLocus).mpr (h x hxc))


-- created on 2026-10-05
