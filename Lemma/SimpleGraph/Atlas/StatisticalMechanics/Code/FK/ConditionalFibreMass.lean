import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.ConditionalFibreMass
open StatMech StatMech.FK


/--
[condBcProb_event_fibre_eq_mass_mul_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConditionalFibreMass.lean)
-/
@[path]
private lemma condBcProb_event_fibre_eq_mass_mul_cond_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {p q : Real}
  {F : Finset (Sym2 V)}
  {psi : ConfigSpace (Sym2 V)}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ rho ∈ condFibre F psi, A.indicator (fun _ => (1 : Real)) rho * bcProb G C p q rho) = (∑ sigma ∈ condFibre F psi, bcProb G C p q sigma) * (∑ rho, A.indicator (fun _ => (1 : Real)) rho * condBcProb G C p q F psi rho) := by
-- proof
  apply StatMech.FK.condBcProb_event_fibre_eq_mass_mul_cond G C hp hp1 hq F psi A


-- created on 2026-10-23
