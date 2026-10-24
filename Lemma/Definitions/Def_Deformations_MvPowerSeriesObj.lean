import Mathlib
import Lemma.Definitions.Def_Deformations_ProartinianCat

set_option autoImplicit false

universe u

namespace Deformation

open CategoryTheory IsLocalRing MvPowerSeries

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

section Nilpotence

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [IsLocalRing R] [IsProartinian R]

lemma isTopologicallyNilpotent_of_mem_maximalIdeal {x : R} (hx : x ∈ maximalIdeal R) :
    IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent,
    (IsLinearTopology.hasBasis_open_ideal (R := R)).tendsto_right_iff]
  intro I hI
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact hN (Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hx n))

lemma hasEval_of_forall_mem_maximalIdeal {σ : Type*} [Finite σ] {x : σ → R}
    (hx : ∀ j, x j ∈ maximalIdeal R) : MvPowerSeries.HasEval x where
  hpow j := isTopologicallyNilpotent_of_mem_maximalIdeal (hx j)
  tendsto_zero := by
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

end Nilpotence

section Object

open MvPowerSeries.WithPiTopology

variable (𝓞 : Type u) [CommRing 𝓞] (σ : Type)

omit [CommRing 𝓞] in

lemma compactSpace_mvPowerSeries [TopologicalSpace 𝓞] [CompactSpace 𝓞] :
    CompactSpace (MvPowerSeries σ 𝓞) :=
  inferInstanceAs (CompactSpace ((σ →₀ ℕ) → 𝓞))

lemma X_mem_maximalIdeal [IsLocalRing 𝓞] (j : σ) :
    MvPowerSeries.X j ∈ maximalIdeal (MvPowerSeries σ 𝓞) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact fun h => h.ne_zero rfl

lemma isProartinian_mvPowerSeries [IsLocalRing 𝓞] [IsNoetherianRing 𝓞] [TopologicalSpace 𝓞]
    [IsTopologicalRing 𝓞] [IsAdicTopology 𝓞] [CompactSpace 𝓞] :
    IsProartinian (MvPowerSeries σ 𝓞) := by
  haveI : CompactSpace (MvPowerSeries σ 𝓞) := compactSpace_mvPowerSeries 𝓞 σ
  exact
    { isArtinianRing_quotient := fun I hI => by
        have : Finite (MvPowerSeries σ 𝓞 ⧸ I) := AddSubgroup.quotient_finite_of_isOpen _ hI
        exact isArtinian_of_finite }

lemma isLocalHom_algebraMap_mvPowerSeries [IsLocalRing 𝓞] :
    IsLocalHom (algebraMap 𝓞 (MvPowerSeries σ 𝓞)) := by
  constructor
  intro a ha
  rw [← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_C] at ha
  exact ha

lemma isResidueAlgebra_mvPowerSeries [IsLocalRing 𝓞] :
    IsResidueAlgebra 𝓞 (MvPowerSeries σ 𝓞) := by
  constructor
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨MvPowerSeries.constantCoeff f, ?_⟩
  show residue _ _ = residue _ _
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]
  simp [← MvPowerSeries.c_eq_algebraMap]

lemma isLocalProartinianAlgebra_mvPowerSeries [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
    [TopologicalSpace 𝓞] [IsTopologicalRing 𝓞] [IsAdicTopology 𝓞] [CompactSpace 𝓞] :
    IsLocalProartinianAlgebra 𝓞 (MvPowerSeries σ 𝓞) := by
  haveI : IsProartinian (MvPowerSeries σ 𝓞) := isProartinian_mvPowerSeries 𝓞 σ
  haveI : IsLocalHom (algebraMap 𝓞 (MvPowerSeries σ 𝓞)) :=
    isLocalHom_algebraMap_mvPowerSeries 𝓞 σ
  haveI : IsResidueAlgebra 𝓞 (MvPowerSeries σ 𝓞) := isResidueAlgebra_mvPowerSeries 𝓞 σ
  exact ⟨⟩

end Object

section Category

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
variable [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]

noncomputable def mvPowerSeriesObj (n : ℕ) : ProartinianCat 𝓞 where
  carrier := MvPowerSeries (Fin n) 𝓞
  topologicalSpace :=
    letI := (maximalIdeal 𝓞).adicTopology
    WithPiTopology.instTopologicalSpace 𝓞
  isLocalProartinianAlgebra :=
    letI := (maximalIdeal 𝓞).adicTopology
    letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
    letI : IsAdicTopology 𝓞 := ⟨rfl⟩
    letI : CompactSpace 𝓞 := compactSpace_of_finite_residueField
    isLocalProartinianAlgebra_mvPowerSeries 𝓞 (Fin n)

variable {𝓞}

noncomputable def mvPowerSeriesObjX {n : ℕ} (j : Fin n) : (mvPowerSeriesObj 𝓞 n).carrier :=
  MvPowerSeries.X j

lemma mvPowerSeriesObjX_mem_maximalIdeal {n : ℕ} (j : Fin n) :
    mvPowerSeriesObjX (𝓞 := 𝓞) j ∈ maximalIdeal (mvPowerSeriesObj 𝓞 n).carrier :=
  X_mem_maximalIdeal 𝓞 (Fin n) j

end Category

end ProartinianCat

end Deformation
