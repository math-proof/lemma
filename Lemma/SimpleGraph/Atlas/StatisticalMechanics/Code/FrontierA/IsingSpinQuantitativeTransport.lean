import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinQuantitativeTransport
open Filter Topology StatMech StatMech.FrontierA StatMech.FrontierA.SpinConformalTransportEstimate


/--
[tendsto_discreteDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinQuantitativeTransport.lean)
-/
@[path]
private lemma tendsto_discreteDerivative_eq
  [Fintype ι]
  {transport : SpinConformalTransportEstimate Φ a source target}
  {i : ι} :
-- imply
  Tendsto (fun n ↦ transport.discreteDerivative n i) atTop (nhds (deriv Φ (a i))) := by
-- proof
  apply StatMech.FrontierA.SpinConformalTransportEstimate.tendsto_discreteDerivative transport i

/--
[tendsto_spinDerivativeFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinQuantitativeTransport.lean)
-/
@[path]
private lemma tendsto_spinDerivativeFactor_eq
  [Fintype ι]
  {transport : SpinConformalTransportEstimate Φ a source target} :
-- imply
  Tendsto (fun n ↦ spinDerivativeFactor (transport.discreteDerivative n)) atTop (nhds (spinConformalFactor Φ a)) := by
-- proof
  apply StatMech.FrontierA.SpinConformalTransportEstimate.tendsto_spinDerivativeFactor transport

/--
[correlation_residual_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinQuantitativeTransport.lean)
-/
@[path]
private lemma correlation_residual_tendsto_eq
  [Fintype ι]
  {transport : SpinConformalTransportEstimate Φ a source target} :
-- imply
  Tendsto (fun n ↦ target n - spinDerivativeFactor (transport.discreteDerivative n) * source n) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.SpinConformalTransportEstimate.correlation_residual_tendsto transport

/--
[target_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinQuantitativeTransport.lean)
-/
@[path]
private lemma target_tendsto_eq
  [Fintype ι]
  {transport : SpinConformalTransportEstimate Φ a source target}
  {limit : Real}
-- given
  (hsource : Tendsto source atTop (nhds limit)) :
-- imply
  Tendsto target atTop (nhds (spinConformalFactor Φ a * limit)) := by
-- proof
  apply StatMech.FrontierA.SpinConformalTransportEstimate.target_tendsto transport hsource

/--
[target_tendsto_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinQuantitativeTransport.lean)
-/
@[path]
private lemma target_tendsto_comp_eq
  [Fintype ι]
  {Ψ : Complex → Complex}
  {middle final : Nat → Real}
  {first : SpinConformalTransportEstimate Φ a source middle}
  {second : SpinConformalTransportEstimate Ψ (Φ ∘ a) middle final}
  {limit : Real}
-- given
  (hsource : Tendsto source atTop (nhds limit))
  (hΦ : ∀ i, DifferentiableAt Complex Φ (a i))
  (hΨ : ∀ i, DifferentiableAt Complex Ψ (Φ (a i))) :
-- imply
  Tendsto final atTop (nhds (spinConformalFactor (Ψ ∘ Φ) a * limit)) := by
-- proof
  apply StatMech.FrontierA.SpinConformalTransportEstimate.target_tendsto_comp first second hsource hΦ hΨ

/--
[tendsto_squareBoxRenormalizedSpinCorrelation_of_quantitative_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinQuantitativeTransport.lean)
-/
@[path]
private lemma tendsto_squareBoxRenormalizedSpinCorrelation_of_quantitative_transport_eq
  {ι : Type*}
  [Fintype ι]
  {δ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
  {Φ : Complex → Complex}
  {a : ι → Complex}
  {limit : Real}
  {transport : SpinConformalTransportEstimate Φ a (squareBoxRenormalizedSpinCorrelation ι δ β h sourceRadius sourceMarked) (squareBoxRenormalizedSpinCorrelation ι δ β h targetRadius targetMarked)}
-- given
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (hsource : Tendsto (squareBoxRenormalizedSpinCorrelation ι δ β h sourceRadius sourceMarked) atTop (nhds limit)) :
-- imply
  Tendsto (squareBoxRenormalizedSpinCorrelation ι δ β h targetRadius targetMarked) atTop (nhds (spinConformalFactor Φ a * limit)) := by
-- proof
  apply StatMech.FrontierA.tendsto_squareBoxRenormalizedSpinCorrelation_of_quantitative_transport ι δ β h sourceRadius targetRadius sourceMarked targetMarked Φ a limit transport hsource


-- created on 2026-10-23
