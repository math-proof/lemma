import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectAdaptiveFibreLower
open StatMech StatMech.FrontierD


/--
[fkRectCriticalEventMass_adaptive_fibre_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAdaptiveFibreLower.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_adaptive_fibre_lower_eq
  {R : FKRectTorus}
  {q : Real}
  {Base Goal : Set R.Configuration}
  {c : Real}
-- given
  (hq : 0 < q)
  (P : R.Configuration -> R.Configuration)
  (hP : forall omega, P (P omega) = P omega)
  (Arm : R.Configuration -> Set R.Configuration)
  (hBase : forall {omega rho}, P omega = P rho -> (omega ∈ Base ↔ rho ∈ Base))
  (hglue : forall {omega}, omega ∈ Base -> omega ∈ Arm (P omega) -> omega ∈ Goal)
  (hfloor : forall psi, psi ∈ Finset.univ.image P -> c * (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), fkRectCriticalRandomClusterProb R q omega) <= ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), (Arm psi).indicator (fun omega => fkRectCriticalRandomClusterProb R q omega) omega) :
-- imply
  c * fkRectCriticalEventMass R q Base <= fkRectCriticalEventMass R q Goal := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_adaptive_fibre_lower R hq P hP Base Goal Arm c hBase hglue hfloor

/--
[fkRectCritical_rsw_stopping_sixth_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAdaptiveFibreLower.lean)
-/
@[path]
private lemma fkRectCritical_rsw_stopping_sixth_power_eq
  {R : FKRectTorus}
  {q alpha c : Real}
  {E0 E1 Goal : Set R.Configuration}
-- given
  (hq : 1 <= q)
  (halpha : 0 <= alpha)
  (hc : 0 <= c)
  (hE0inc : IsIncreasing E0)
  (hE1inc : IsIncreasing E1)
  (hE0 : alpha ^ 3 / 4 <= fkRectCriticalEventMass R q E0)
  (hE1 : alpha ^ 3 / 4 <= fkRectCriticalEventMass R q E1)
  (P : R.Configuration -> R.Configuration)
  (hP : forall omega, P (P omega) = P omega)
  (Arm : R.Configuration -> Set R.Configuration)
  (hBase : forall {omega rho}, P omega = P rho -> (omega ∈ E0 ∩ E1 ↔ rho ∈ E0 ∩ E1))
  (hglue : forall {omega}, omega ∈ E0 ∩ E1 -> omega ∈ Arm (P omega) -> omega ∈ Goal)
  (hfloor : forall psi, psi ∈ Finset.univ.image P -> c * (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), fkRectCriticalRandomClusterProb R q omega) <= ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), (Arm psi).indicator (fun omega => fkRectCriticalRandomClusterProb R q omega) omega) :
-- imply
  c * (alpha ^ 6 / 16) <= fkRectCriticalEventMass R q Goal := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_rsw_stopping_sixth_power R hq halpha hc E0 E1 Goal hE0inc hE1inc hE0 hE1 P hP Arm hBase hglue hfloor


-- created on 2026-10-23
