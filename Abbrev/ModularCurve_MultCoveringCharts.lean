import Structure.AlgebraicCurve_SemistableCharts
import Def.AlgebraicCurve_ChordalProximity
import Def.ModularCurve_SupersingularModuli
import Structure.ModularCurve_LevelOneProlongationPair
import Lemma.AlgebraicCurve.SemistableChartsComap
import Structure.ModularCurve_LevelOneChartFst
import Instance.ModularCurve_MultCoveringCharts
import Structure.ModularCurve_MultCoveringCharts

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

abbrev jF (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩

abbrev jpF (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_mul_left p 1))⟩

abbrev tieG (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) := jpF p - jF p ^ p

abbrev jBar (k : Type) [Field k] : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

abbrev nCharts : ℕ := 2


abbrev Fbar (A : ValuationSubring (AlgebraicClosure ℚ)) (_i : Fin nCharts) : Type :=
  ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)

abbrev IsSSCentred (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (a : IsLocalRing.ResidueField ↥A) : Prop :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsSSCentred A p W a


section PerA

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

end PerA

end ModularCurve.MultCovering

end
