import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
open SimpleGraph StatMech StatMech.FK


/--
[ecz_closeOff_apply_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigEventLaw.lean)
-/
@[path]
private lemma ecz_closeOff_apply_edge_eq
  [Fintype V]
  [DecidableEq V]
  {omega : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (he : e ∈ G.edgeFinset) :
-- imply
  (ecz_closeOff G omega).1 e = omega e := by
-- proof
  apply StatMech.FK.ecz_closeOff_apply_edge omega he

/--
[ecz_closeOff_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigEventLaw.lean)
-/
@[path]
private lemma ecz_closeOff_val_eq
  [Fintype V]
  [DecidableEq V]
  {omega : ecz_ClosedOff G} :
-- imply
  ecz_closeOff G omega.1 = omega := by
-- proof
  apply StatMech.FK.ecz_closeOff_val omega

/--
[ecz_eventWeight_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigEventLaw.lean)
-/
@[path]
private lemma ecz_eventWeight_factorization_eq
  [Fintype V]
  [DecidableEq V]
  {p q : Real}
  {A : Set (ecz_ClosedOff G)} :
-- imply
  (∑ omega : ConfigSpace (Sym2 V), (ecz_closeOff G ⁻¹' A).indicator (fun omega => fkWeight G p q omega) omega) = 2 ^ ecz_NE G * ecz_eventWeight G p q A := by
-- proof
  apply StatMech.FK.ecz_eventWeight_factorization p q A

/--
[ecz_eventProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigEventLaw.lean)
-/
@[path]
private lemma ecz_eventProb_eq_eq
  [Fintype V]
  [DecidableEq V]
  {p q : Real}
  {A : Set (ecz_ClosedOff G)} :
-- imply
  (∑ omega : ConfigSpace (Sym2 V), (ecz_closeOff G ⁻¹' A).indicator (fun _ => (1 : Real)) omega * fkProb G p q omega) = ecz_eventWeight G p q A / ecz_fkZEdge G p q := by
-- proof
  apply StatMech.FK.ecz_eventProb_eq p q A


-- created on 2026-10-23
