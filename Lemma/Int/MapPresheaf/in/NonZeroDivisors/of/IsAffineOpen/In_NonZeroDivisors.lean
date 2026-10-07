import Mathlib
import sympy.Basic

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite

/--
[AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R]
  {Y : Scheme.{u}}
  {f : Y ⟶ Spec (CommRingCat.of R)} [Flat f]
  {r : R}
  {U : Y.Opens}
-- given
  (hr : r ∈ nonZeroDivisors R)
  (hU : IsAffineOpen U) :
-- imply
  Y.presheaf.map (homOfLE le_top).op (f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      ∈ nonZeroDivisors Γ(Y, U) := by
-- proof
  have happ : Y.presheaf.map (homOfLE le_top).op (f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      = (f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [happ]
  have hflat : (f.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat f inferInstance ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ ⟨U, hU⟩ le_top

  let e : R ≃+* Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  let φ : R →+* Γ(Y, U) := (f.appLE ⊤ U le_top).hom.comp e.toRingHom
  have hφflat : φ.Flat := (RingHom.Flat.of_bijective e.bijective).comp hflat
  let := φ.toAlgebra
  have : Module.Flat R Γ(Y, U) := hφflat
  have hreg : IsSMulRegular Γ(Y, U) r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have hφr : φ r = (f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := rfl
  rw [← hφr]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hreg
  show r • x = r • (0 : Γ(Y, U))
  rw [smul_zero, Algebra.smul_def]
  show φ r * x = 0
  rw [mul_comm]; exact hx


-- created on 2026-10-05
