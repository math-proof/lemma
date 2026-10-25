import Mathlib
import Lemma.AutomorphicForm.FundamentalDomainVolume
import Lemma.UpperHalfPlane.SiegelSetCover
import Instance.AutomorphicForm_Gamma0FundamentalSet
import Def.AutomorphicForm_Gamma0FundamentalSet

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise

namespace FLT.Gamma0FundamentalSet


theorem mem_gammaFundamentalSet_iff {Γ : Subgroup SL(2, ℤ)} {z : ℍ} :
    z ∈ gammaFundamentalSet Γ ↔ ∃ q : SL(2, ℤ) ⧸ Γ, Quotient.out q • z ∈ 𝒟 := by
  simp only [gammaFundamentalSet, Set.mem_iUnion, Set.mem_inv_smul_set_iff]

theorem exists_smul_mem_gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ γ ∈ Γ, γ • z ∈ gammaFundamentalSet Γ :=
  FLT.SiegelSetCover.exists_smul_mem_iUnion_smul_fd Γ z

theorem gammaFundamentalSet_eq_biUnion (Γ : Subgroup SL(2, ℤ)) [Finite (SL(2, ℤ) ⧸ Γ)] :
    haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
    gammaFundamentalSet Γ =
      ⋃ γ ∈ (Finset.univ.image fun q : SL(2, ℤ) ⧸ Γ => (Quotient.out q)⁻¹), γ • 𝒟 := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  ext z
  simp only [gammaFundamentalSet, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨fun ⟨q, hq⟩ => ⟨_, ⟨q, rfl⟩, hq⟩, fun ⟨γ, ⟨q, hq⟩, hz⟩ => ⟨q, hq ▸ hz⟩⟩

theorem volume_gammaFundamentalSet_lt_top (Γ : Subgroup SL(2, ℤ))
    [Finite (SL(2, ℤ) ⧸ Γ)] : volume (gammaFundamentalSet Γ) < ⊤ := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  rw [gammaFundamentalSet_eq_biUnion Γ]
  exact FLT.FundamentalDomainVolume.volume_biUnion_smul_fd_lt_top _

theorem volume_gammaFundamentalSet_pos (Γ : Subgroup SL(2, ℤ)) :
    0 < volume (gammaFundamentalSet Γ) := by
  refine lt_of_lt_of_le ?_
    (measure_mono (Set.subset_iUnion _ (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ)))
  rw [FLT.HyperbolicMeasure.volume_smul_sl2z]
  exact FLT.FundamentalDomainVolume.volume_fd_pos

theorem volume_gammaFundamentalSet_ne_zero_ne_top (Γ : Subgroup SL(2, ℤ))
    [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) ≠ 0 ∧ volume (gammaFundamentalSet Γ) ≠ ⊤ :=
  ⟨(volume_gammaFundamentalSet_pos Γ).ne', (volume_gammaFundamentalSet_lt_top Γ).ne⟩

theorem volume_gamma0_lt_top (N : ℕ) [NeZero N] :
    volume (gammaFundamentalSet (Gamma0 N)) < ⊤ :=
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  volume_gammaFundamentalSet_lt_top (Gamma0 N)

theorem exists_gamma0_smul_mem (N : ℕ) (z : ℍ) :
    ∃ γ ∈ Gamma0 N, γ • z ∈ gammaFundamentalSet (Gamma0 N) :=
  exists_smul_mem_gammaFundamentalSet (Gamma0 N) z


theorem isCompact_smul_truncated (γ : SL(2, ℤ)) (y : ℝ) :
    IsCompact (γ • truncatedFundamentalDomain y) :=
  IsCompact.smul γ (isCompact_truncatedFundamentalDomain y)

theorem isCompact_truncatedGammaFundamentalSet (Γ : Subgroup SL(2, ℤ))
    [Finite (SL(2, ℤ) ⧸ Γ)] (y : ℝ) :
    IsCompact (truncatedGammaFundamentalSet Γ y) :=
  isCompact_iUnion fun q => isCompact_smul_truncated (Quotient.out q)⁻¹ y

theorem isCompact_truncatedGamma0 (N : ℕ) [NeZero N] (y : ℝ) :
    IsCompact (truncatedGammaFundamentalSet (Gamma0 N) y) :=
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  isCompact_truncatedGammaFundamentalSet (Gamma0 N) y

theorem truncatedGammaFundamentalSet_subset (Γ : Subgroup SL(2, ℤ)) (y : ℝ) :
    truncatedGammaFundamentalSet Γ y ⊆ gammaFundamentalSet Γ := by
  refine Set.iUnion_mono fun q => Set.smul_set_mono ?_
  exact fun z hz => hz.1

theorem gate_volume_lt_volume_univ (Γ : Subgroup SL(2, ℤ)) [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) < volume (Set.univ : Set ℍ) := by
  rw [FLT.HyperbolicMeasure.volume_univ_eq_top]
  exact volume_gammaFundamentalSet_lt_top Γ

theorem gate_volume_top_eq : volume (gammaFundamentalSet (⊤ : Subgroup SL(2, ℤ))) =
    volume 𝒟 := by
  haveI : Subsingleton (SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))) :=
    QuotientGroup.subsingleton_quotient_top
  have huniq : ∀ q : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ)),
      q = (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))) := fun q =>
    Subsingleton.elim _ _
  have : gammaFundamentalSet (⊤ : Subgroup SL(2, ℤ)) =
      (Quotient.out (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))))⁻¹ • 𝒟 := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun q => ?_)
      (Set.subset_iUnion (fun q : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ)) =>
        (Quotient.out q)⁻¹ • 𝒟) (QuotientGroup.mk 1))
    rw [huniq q]
  rw [this, FLT.HyperbolicMeasure.volume_smul_sl2z]

example : volume (gammaFundamentalSet (Gamma0 11)) < ⊤ := volume_gamma0_lt_top 11

theorem gate_truncated_nonempty (Γ : Subgroup SL(2, ℤ)) :
    (truncatedGammaFundamentalSet Γ 2).Nonempty := by
  refine ⟨(Quotient.out (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ))⁻¹ • UpperHalfPlane.ρ,
    Set.mem_iUnion.mpr ⟨QuotientGroup.mk 1, Set.smul_mem_smul_set ?_⟩⟩
  refine ⟨FLT.SiegelSetCover.gate_rho_mem_fd, ?_⟩
  rw [FLT.SiegelSetCover.gate_im_rho]
  nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0),
    Real.sqrt_nonneg (3 : ℝ)]

end FLT.Gamma0FundamentalSet
