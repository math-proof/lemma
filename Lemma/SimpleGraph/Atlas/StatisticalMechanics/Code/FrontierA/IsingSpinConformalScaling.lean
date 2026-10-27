import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinConformalScaling.Part2
open Filter Topology StatMech StatMech.FrontierA


/--
[spinMeshRenormalization_eq_card_div_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalScaling.lean)
-/
@[path]
private lemma spinMeshRenormalization_eq_card_div_eight_eq
  {iota : Type*}
  [Fintype iota]
  {delta : Real} :
-- imply
  spinMeshRenormalization iota delta = delta ^ (-(Fintype.card iota : Real) / 8) := by
-- proof
  apply StatMech.FrontierA.spinMeshRenormalization_eq_card_div_eight iota delta

/--
[spinRenormalizedCorrelation_eq_delta_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalScaling.lean)
-/
@[path]
private lemma spinRenormalizedCorrelation_eq_delta_pow_eq
  {iota : Type*}
  [Fintype iota]
  {delta correlation : Nat → Real}
  {n : Nat} :
-- imply
  spinRenormalizedCorrelation iota delta correlation n = delta n ^ (-(Fintype.card iota : Real) / 8) * correlation n := by
-- proof
  apply StatMech.FrontierA.spinRenormalizedCorrelation_eq_delta_pow iota delta correlation n

/--
[tendsto_spinRenormalizedCorrelation_of_asymptotic_conformal_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalScaling.lean)
-/
@[path]
private lemma tendsto_spinRenormalizedCorrelation_of_asymptotic_conformal_transport_eq
  [Fintype iota]
  {delta : Nat → Real}
  {localFactor : Nat → iota → Real}
  {Phi : Complex → Complex}
  {a : iota → Complex}
  {sourceRaw targetRaw : Nat → Real}
  {limit : Real}
-- given
  (hlocal : ∀ i, Tendsto (fun n ↦ localFactor n i) atTop (nhds (norm (deriv Phi (a i)) ^ isingSpinScalingDimension)))
  (hsource : Tendsto (spinRenormalizedCorrelation iota delta sourceRaw) atTop (nhds limit))
  (htransport : Tendsto (fun n ↦ spinRenormalizedCorrelation iota delta targetRaw n - (∏ i, localFactor n i) * spinRenormalizedCorrelation iota delta sourceRaw n) atTop (nhds 0)) :
-- imply
  Tendsto (spinRenormalizedCorrelation iota delta targetRaw) atTop (nhds (spinConformalFactor Phi a * limit)) := by
-- proof
  apply StatMech.FrontierA.tendsto_spinRenormalizedCorrelation_of_asymptotic_conformal_transport delta localFactor Phi a sourceRaw targetRaw limit hlocal hsource htransport


-- created on 2026-10-23
