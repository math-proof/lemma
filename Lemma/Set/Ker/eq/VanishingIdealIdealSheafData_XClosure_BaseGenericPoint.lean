import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_Hom_ker_eq_vanishingIdeal_closure_singleton_genericPoint](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_ker_eq_vanishingIdeal_closure_singleton_genericPoint.lean)
-/
@[path]
private lemma main
  {C Y : Scheme.{u}} [IsIntegral C]
  {f : C ⟶ Y} [QuasiCompact f] :
-- imply
  f.ker = Scheme.IdealSheafData.vanishingIdeal (X :=
-- proof
  Y) ⟨closure ({f.base (genericPoint C)} : Set Y), isClosed_closure⟩ := by
   classical

   have hsupp : (f.ker.support : Set Y) = closure ({f.base (genericPoint C)} : Set Y) := by
     rw [Scheme.Hom.support_ker]
     apply le_antisymm
     · refine closure_minimal ?_ isClosed_closure
       rintro _ ⟨c, rfl⟩
       exact specializes_iff_mem_closure.mp ((genericPoint_specializes c).map f.base.hom.continuous)
     · exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint C, rfl⟩)
   have hZ : (⟨closure ({f.base (genericPoint C)} : Set Y), isClosed_closure⟩ : TopologicalSpace.Closeds Y) = f.ker.support :=
     TopologicalSpace.Closeds.ext hsupp.symm
   rw [hZ, Scheme.IdealSheafData.vanishingIdeal_support]

   ext U : 2
   rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
   exact ((Ideal.isRadical_bot (R := Γ(C, f ⁻¹ᵁ U))).comap (f.app U).hom).radical.symm


-- created on 2026-10-05
