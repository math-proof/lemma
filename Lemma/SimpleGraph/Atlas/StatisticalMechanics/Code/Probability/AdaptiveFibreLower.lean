import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.AdaptiveFibreLower
open StatMech StatMech.Probability


/--
[finiteEventMass_adaptive_fibre_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/AdaptiveFibreLower.lean)
-/
@[path]
private lemma finiteEventMass_adaptive_fibre_lower_eq
  [Fintype Omega]
  [DecidableEq Omega]
  {Base Goal : Set Omega}
  {c : Real}
-- given
  (mu : Omega -> Real)
  (hmu : forall omega, 0 <= mu omega)
  (P : Omega -> Omega)
  (hP : forall omega, P (P omega) = P omega)
  (Arm : Omega -> Set Omega)
  (hBase : forall {omega rho}, P omega = P rho -> (omega ∈ Base ↔ rho ∈ Base))
  (hglue : forall {omega}, omega ∈ Base -> omega ∈ Arm (P omega) -> omega ∈ Goal)
  (hfloor : forall psi, psi ∈ Finset.univ.image P -> c * (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), mu omega) <= ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), (Arm psi).indicator mu omega) :
-- imply
  c * finiteEventMass mu Base <= finiteEventMass mu Goal := by
-- proof
  apply StatMech.Probability.finiteEventMass_adaptive_fibre_lower mu hmu P hP Base Goal Arm c hBase hglue hfloor


-- created on 2026-10-23
