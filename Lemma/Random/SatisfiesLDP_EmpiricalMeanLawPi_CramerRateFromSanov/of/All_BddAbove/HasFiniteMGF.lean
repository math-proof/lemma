import Def.ProbabilityTheory.CramerTheorem
import Lemma.Random.SatisfiesLDP
import Theorem.v1.Atlas.TheoryOfProbability.code.CramerBarycenter
import Theorem.v1.Atlas.TheoryOfProbability.code.CramerRateIDCore
open Filter MeasureTheory ProbabilityMeasure Random Set
open scoped ENNReal Topology InnerProductSpace


/--
Sanov-contracted empirical-mean LDP under `HasFiniteMGF` + global FY
`BddAbove` (`ForallBddAbove`), with rate `cramerRateFromSanov`.
-/
@[path]
private lemma main
  {d : ℕ}
  {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
-- given
  (hMGF : HasFiniteMGF μ₀)
  (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
    BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
-- imply
  SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n) (cramerRateFromSanov μ₀) := by
-- proof
  apply
    ((satisfiesLDP_of_gammaApprox_of_bounds
        (fun n => Measure.pi fun _ : Fin n => μ₀)
        (fun n => sampleMeanPi (d := d) (n := n))
        (fun R n => sampleClampMeanPi' (d := d) (n := n) R)
        (fun n => measurable_sampleMeanPi (d := d) (n := n))
        (fun R n => measurable_sampleClampMeanPi' (d := d) (n := n) R)
        (EventuallyExpGoodApprox_sampleMean_sampleClampMeanPi' hMGF)
        (clampContractedRate μ₀)
        (fun R U hU =>
          liminf_log_map_sampleClampMeanPi'_ge_iInf_clampContractedRate μ₀ R hU)
        (fun R F hF =>
          limsup_log_map_sampleClampMeanPi'_le_iInf_clampContractedRate μ₀ R hF)
        (HasCompactFiniteLevelSets_gammaLiminfRate_clampContractedRate hMGF hbdd)
        (fun G hG => hClosed_gammaLiminfRate_clampContractedRate hMGF hbdd G hG)
        (IsRateFunction_gammaLiminfRate_clampContractedRate hMGF hbdd)).congr_measure_of_eventually_eq
      _).congr_rate
      (fun y => gammaLiminfRate_clampContractedRate_eq_cramerRateFromSanov hMGF hbdd y)
      ((funext
          (cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid
            μ₀ hMGF (TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd) hbdd)) ▸
        lowerSemicontinuous_cramerRateFunction_of_HasFiniteMGF μ₀ hMGF hbdd)
  ·
    filter_upwards [eventually_gt_atTop 0] with n hn
    apply (empiricalMeanLawPi_eq_map_sampleMeanPi (μ := μ₀) hn).symm


-- created on 2026-11-04
