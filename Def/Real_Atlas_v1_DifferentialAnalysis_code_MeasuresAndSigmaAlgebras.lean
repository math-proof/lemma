module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras.Part3

@[expose] public section

open MeasureTheory Set MeasuresAndSigmaAlgebras
open scoped ENNReal
open scoped NNReal
open CompactlySupportedContinuousMap
open Measure RealRMK
open scoped CompactlySupported ZeroAtInfty


namespace MeasuresAndSigmaAlgebras

/--
[outerMeasure_isOuterMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[lebesgue_borel_le_caratheodory](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[isOuterMeasureMeasurable_iff_isCaratheodory](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
section CaratheodoryMeasurable
variable {X : Type*} (μ : OuterMeasure X)
/-- The σ-algebra of Carathéodory-measurable sets for an outer measure `μ`. -/
@[reducible] def caratheodorySigmaAlgebra : SigmaAlgebra X := μ.caratheodory
end CaratheodoryMeasurable

namespace MeasuresAndSigmaAlgebras

/--
[isOuterMeasureMeasurable_of_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[caratheodoryMeasure_isComplete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[caratheodory_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/

namespace MeasuresAndSigmaAlgebras

/--
[isOpen_outerMeasureMeasurable_and_measure_eq_innerContent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
section RieszMeasureRadon
open Measure RealRMK
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]
  (Λ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ)

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[prop_2_8_radon_measure_from_C0_functional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[borel_le_caratheodory_of_openSets_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
end MeasuresAndSigmaAlgebras


-- created on 2026-10-23

end
