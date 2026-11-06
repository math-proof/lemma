import Lemma.Random.SatisfiesLDP_EmpiricalMeanLawPi_CramerRateFromSanov.of.All_BddAbove.HasFiniteMGF
open MeasureTheory ProbabilityMeasure Random Set
open scoped ENNReal Topology InnerProductSpace


/--
Cramér's theorem for product empirical means under vector MGF + global FY
`BddAbove` (`ForallBddAbove` — the intentional public gate beyond bare
`HasFiniteMGF`; compact / lattice / degenerate laws can have MGF with
`Λ* = ∞` off `conv(supp)`).

Wiring: Sanov-contracted mean LDP (`cramerRateFromSanov`) → rate ID to
`cramerRateFunction` (`TiltCover`, CRF lsc).
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
  SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n)
    (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) := by
-- proof
  apply
    (SatisfiesLDP_EmpiricalMeanLawPi_CramerRateFromSanov.of.All_BddAbove.HasFiniteMGF
      hMGF hbdd).congr_rate
    (cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid μ₀ hMGF
      (TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd) hbdd)
    (lowerSemicontinuous_cramerRateFunction_of_HasFiniteMGF μ₀ hMGF hbdd)


-- created on 2026-11-03
-- updated on 2026-11-04
