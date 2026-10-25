import Structure.AlgebraicCurve_SemistableCharts
import Def.AlgebraicCurve_ChordalProximity
import Def.ModularCurve_SupersingularModuli
import Structure.ModularCurve_LevelOneProlongationPair
import Lemma.AlgebraicCurve.SemistableChartsComap
import Structure.ModularCurve_LevelOneChartFst
import Instance.ModularCurve_MultCoveringCharts

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve.MultCovering

section Instances
variable (A : ValuationSubring (AlgebraicClosure ℚ))

end Instances


def mAnnuli (p : ℕ) : ℕ := p / 12 + (if p % 3 = 2 then 1 else 0) + (if p % 4 = 3 then 1 else 0)


structure ChartCtx (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] where
  data  : ModularPolynomialData p
  hKr   : KroneckerCongruence p data
  hα    : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p
  hβ    : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p
  P     : PlaceSpecialization A p 1 data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ
  R     : P.LevelOneProlongationPair

  S₁    : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))

  Wn    : Finset (Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
  hWn   : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (IsLocalRing.ResidueField ↥A)

  hfin  : (ssJSet p (IsLocalRing.ResidueField ↥A)).Finite
  hcard : hfin.toFinset.card = mAnnuli p

  supply : R.ChartFstSupply S₁

section PerA

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)


end PerA


end ModularCurve.MultCovering

end
