import Def.v1.Atlas.TheoryOfProbability.code.CramerTheorem
import Lemma.Random.SatisfiesLDP
import Theorem.v1.Atlas.TheoryOfProbability.code.CramerBarycenter
import Theorem.v1.Atlas.TheoryOfProbability.code.CramerRateID
import Theorem.v1.Atlas.TheoryOfProbability.code.CramerTheorem
open MeasureTheory ProbabilityMeasure Random Set
open scoped ENNReal Topology InnerProductSpace


/--
Cramér's theorem for product empirical means under vector MGF + global FY
`BddAbove` (`ForallBddAbove` — the intentional public gate beyond bare
`HasFiniteMGF`; compact / lattice / degenerate laws can have MGF with
`Λ* = ∞` off `conv(supp)`).

Wiring: Cont+Meas barycenter →
`satisfiesLDP_empiricalMeanLawPi_cramerRateFromSanov_of_continuous_barycenter`
→ `cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove` (TiltCover, CRF lsc, and
fiber `hid` all internalized). Residuals Cont/Meas: true barycenter continuity
on raw `ProbabilityMeasure (ℝᵈ)` needs moment restrictions; clamp /
`UniformExpMoment` paths still need R→∞ / exp-tightness for the untruncated
`empiricalMeanLawPi` statement.
-/
@[path]
private lemma main
  {d : ℕ}
  {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
-- given
  (hMGF : HasFiniteMGF μ₀)
  (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
    BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
  (hbaryCont : Continuous (barycenter : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) → _))
  (hbaryMeas : Measurable (barycenter : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) → _)) :
-- imply
  SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n)
    (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) :=
-- proof
by
  have hcover := TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd
  have hRate :=
    lowerSemicontinuous_cramerRateFunction_of_HasFiniteMGF μ₀ hMGF hbdd
  have heqRate :=
    cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid μ₀ hMGF hcover hbdd
  have hJ : LowerSemicontinuous (cramerRateFromSanov μ₀) := by
    convert hRate using 1
    exact funext heqRate
  refine cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd ?_
  exact satisfiesLDP_empiricalMeanLawPi_cramerRateFromSanov_of_continuous_barycenter
    μ₀ hbaryCont hbaryMeas hJ


-- created on 2026-11-03
