import Mathlib
import Lemma.AutomorphicForm.Gamma0FundamentalSet
import Lemma.AutomorphicForm.L2AutomorphicCarrier
import Lemma.AutomorphicForm.TruncatedDomainPartition
import Abbrev.AutomorphicForm_L2ProductionInstance

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise ENNReal

noncomputable section

namespace FLT.L2ProductionInstance

open FLT.Gamma0FundamentalSet FLT.L2Carrier

theorem isClosed_smul_fd (γ : SL(2, ℤ)) : IsClosed (γ • 𝒟) :=
  ModularGroup.isClosed_fd.smul γ

theorem measurableSet_smul_fd (γ : SL(2, ℤ)) : MeasurableSet (γ • 𝒟) :=
  (isClosed_smul_fd γ).measurableSet


theorem measurableSet_gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) :
    MeasurableSet (gammaFundamentalSet Γ) :=
  MeasurableSet.iUnion fun q => measurableSet_smul_fd (Quotient.out q)⁻¹

theorem measurableSet_gamma0 (N : ℕ) : MeasurableSet (gammaFundamentalSet (Gamma0 N)) :=
  measurableSet_gammaFundamentalSet (Gamma0 N)


noncomputable def boundedToGamma0L2 (N : ℕ) [NeZero N] (f : ℍ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ z ∈ gammaFundamentalSet (Gamma0 N), ‖f z‖ ≤ C) : Gamma0L2 N :=
  boundedToL2 (volume_gamma0_lt_top N) (measurableSet_gamma0 N) f hf C hC

theorem boundedToGamma0L2_coeFn (N : ℕ) [NeZero N] (f : ℍ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ z ∈ gammaFundamentalSet (Gamma0 N), ‖f z‖ ≤ C) :
    (boundedToGamma0L2 N f hf C hC : ℍ → ℂ)
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] f :=
  boundedToL2_coeFn _ _ f hf C hC

noncomputable def gamma0L2Const (N : ℕ) [NeZero N] : Gamma0L2 N :=
  boundedToGamma0L2 N (fun _ => (1 : ℂ)) continuous_const 1 (fun _ _ => by simp)

theorem gamma0L2Const_ne_zero (N : ℕ) [NeZero N] : gamma0L2Const N ≠ 0 := by
  intro h

  have h1 : (gamma0L2Const N : ℍ → ℂ)
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp h
  have h2 : (fun _ : ℍ => (1 : ℂ))
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] 0 :=
    (boundedToGamma0L2_coeFn N (fun _ => (1 : ℂ)) continuous_const 1
      (fun _ _ => by simp)).symm.trans h1

  have hnull : (volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))
      Set.univ = 0 := by
    have h3 : ∀ᵐ z ∂((volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))),
        (1 : ℂ) = 0 := h2
    simpa [ae_iff] using h3
  rw [Measure.restrict_apply_univ] at hnull
  exact absurd hnull (volume_gammaFundamentalSet_pos (Gamma0 N)).ne'


theorem gate_const_not_memLp_unrestricted :
    ¬ MemLp (fun _ : ℍ => (1 : ℂ)) 2 (volume : Measure ℍ) :=
  gate_const_not_memLp_of_infinite FLT.HyperbolicMeasure.volume_univ_eq_top

example : volume (gammaFundamentalSet (Gamma0 11)) < ⊤ := volume_gamma0_lt_top 11

theorem gate_level_one_volume :
    volume (gammaFundamentalSet (Gamma0 1)) ≤ volume 𝒟 := by

  have hsub : ∀ q : SL(2, ℤ) ⧸ Gamma0 1,
      q = QuotientGroup.mk (1 : SL(2, ℤ)) := fun q => by
    induction q using QuotientGroup.induction_on with
    | _ a => exact (QuotientGroup.eq).mpr (Gamma0_mem.mpr (Subsingleton.elim _ _))
  have hcover : gammaFundamentalSet (Gamma0 1) ⊆
      (Quotient.out (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma0 1))⁻¹ • 𝒟 := by
    refine Set.iUnion_subset fun q => ?_
    rw [hsub q]
  calc volume (gammaFundamentalSet (Gamma0 1))
      ≤ volume ((Quotient.out (QuotientGroup.mk (1 : SL(2, ℤ)) :
          SL(2, ℤ) ⧸ Gamma0 1))⁻¹ • 𝒟) := measure_mono hcover
    _ = volume 𝒟 := FLT.HyperbolicMeasure.volume_smul_sl2z _ _

end FLT.L2ProductionInstance

end
