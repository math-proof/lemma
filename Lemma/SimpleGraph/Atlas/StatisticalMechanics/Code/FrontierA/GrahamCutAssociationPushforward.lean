import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCutAssociationPushforward
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[grahamCutPositiveAssociation_of_fkg_pushforward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutAssociationPushforward.lean)
-/
@[path]
private lemma grahamCutPositiveAssociation_of_fkg_pushforward_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {m : V}
  [Fintype Omega]
  [DistribLattice Omega]
  [OrderBot Omega]
-- given
  (J : Sym2 V -> Real)
  (mu : Omega -> Real)
  (cut : Omega -> Finset V)
  (hmu0 : (0 : Omega -> Real) <= mu)
  (hmu1 : ∑ omega, mu omega = 1)
  (hmuFKG : forall x y, mu x * mu y <= mu (x ⊓ y) * mu (x ⊔ y))
  (hcut : Antitone cut)
  (hpush : forall S : Finset V, isingCutMass G beta J m S = ∑ omega : Omega, if cut omega = S then mu omega else 0) :
-- imply
  GrahamCutPositiveAssociation G beta J m := by
-- proof
  apply StatMech.FrontierA.grahamCutPositiveAssociation_of_fkg_pushforward G beta J m mu cut hmu0 hmu1 hmuFKG hcut hpush


-- created on 2026-10-23
