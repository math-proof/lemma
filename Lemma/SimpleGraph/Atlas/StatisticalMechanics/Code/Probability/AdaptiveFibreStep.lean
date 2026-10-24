import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.AdaptiveFibreStep
open StatMech StatMech.Probability


/--
[finiteEventMass_eq_sum_projectionFibres](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/AdaptiveFibreStep.lean)
-/
@[path]
private lemma finiteEventMass_eq_sum_projectionFibres_eq
  [Fintype Omega]
  [DecidableEq Omega]
  {mu : Omega → Real}
  {P : Omega → Omega}
  {A : Set Omega} :
-- imply
  finiteEventMass mu A = ∑ psi ∈ (Finset.univ.image P), ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), A.indicator mu omega := by
-- proof
  apply StatMech.Probability.finiteEventMass_eq_sum_projectionFibres mu P A

/--
[finiteEventMass_adaptive_fibre_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/AdaptiveFibreStep.lean)
-/
@[path]
private lemma finiteEventMass_adaptive_fibre_step_eq
  [Fintype Omega]
  [DecidableEq Omega]
  {mu : Omega → Real}
  {P : Omega → Omega}
  {Base Inserted : Set Omega}
  {Arm : Omega → Set Omega}
  {a : Real}
-- given
  (hmu : ∀ omega, 0 ≤ mu omega)
  (hP : ∀ omega, P (P omega) = P omega)
  (hBase : ∀ {omega rho}, P omega = P rho → (omega ∈ Base ↔ rho ∈ Base))
  (hInserted : ∀ {omega}, omega ∈ Inserted → omega ∈ Base ∧ omega ∈ Arm (P omega))
  (hcap : ∀ psi ∈ Finset.univ.image P, (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), (Arm psi).indicator mu omega) ≤ a * ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), mu omega) :
-- imply
  finiteEventMass mu Inserted ≤ a * finiteEventMass mu Base := by
-- proof
  apply StatMech.Probability.finiteEventMass_adaptive_fibre_step mu hmu P hP Base Inserted Arm hBase hInserted hcap

/--
[finiteEventMass_adaptive_fibre_step_on_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/AdaptiveFibreStep.lean)
-/
@[path]
private lemma finiteEventMass_adaptive_fibre_step_on_base_eq
  [Fintype Omega]
  [DecidableEq Omega]
  {mu : Omega → Real}
  {P : Omega → Omega}
  {Base Inserted : Set Omega}
  {Arm : Omega → Set Omega}
  {a : Real}
-- given
  (hmu : ∀ omega, 0 ≤ mu omega)
  (hP : ∀ omega, P (P omega) = P omega)
  (hBase : ∀ {omega rho}, P omega = P rho → (omega ∈ Base ↔ rho ∈ Base))
  (hInserted : ∀ {omega}, omega ∈ Inserted → omega ∈ Base ∧ omega ∈ Arm (P omega))
  (hcap : ∀ psi ∈ Finset.univ.image P, psi ∈ Base → (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), (Arm psi).indicator mu omega) ≤ a * ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi), mu omega) :
-- imply
  finiteEventMass mu Inserted ≤ a * finiteEventMass mu Base := by
-- proof
  apply StatMech.Probability.finiteEventMass_adaptive_fibre_step_on_base mu hmu P hP Base Inserted Arm hBase hInserted hcap


-- created on 2026-10-23
