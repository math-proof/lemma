import Mathlib
import Lemma.LocalLanglands.LocalHeckeInstance

set_option autoImplicit false

namespace FLT.SpectralSide


theorem gl2_compactSpace (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R] :
    CompactSpace (GL (Fin 2) R) := inferInstance

theorem isCompact_coe_integralSubgroup (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R]
    (K : Type*) [Field K] [Algebra R K] [TopologicalSpace K]
    (hcont : Continuous (algebraMap R K)) :
    IsCompact ((LocalGL2.integralSubgroup R K : Set (GL (Fin 2) K))) := by
  haveI : CompactSpace (GL (Fin 2) R) := gl2_compactSpace R
  have hmapcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)) := by
    unfold Matrix.GeneralLinearGroup.map
    refine Continuous.units_map _ ?_
    exact continuous_matrix fun i j =>
      hcont.comp ((continuous_apply j).comp (continuous_apply i))
  have hr : IsCompact
      (Set.range ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))) :=
    isCompact_range hmapcont
  simpa [LocalGL2.integralSubgroup, MonoidHom.coe_range] using hr

theorem isCompact_coe_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    IsCompact ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))) :=
  isCompact_coe_integralSubgroup ℤ_[p] ℚ_[p] continuous_subtype_val

theorem compactSpace_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    CompactSpace (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) :=
  isCompact_iff_compactSpace.mp (isCompact_coe_integralSubgroup_padic p)

end FLT.SpectralSide
