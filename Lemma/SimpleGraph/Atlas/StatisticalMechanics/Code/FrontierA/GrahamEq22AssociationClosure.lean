import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamEq22AssociationClosure
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamEq22_correction_upper_bound_of_cutPositiveAssociation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamEq22AssociationClosure.lean)
-/
@[path]
private lemma grahamEq22_correction_upper_bound_of_cutPositiveAssociation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m)
  (hassoc : GrahamCutPositiveAssociation G beta J m) :
-- imply
  let Z := currentSum G beta J ∅ let Cim := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m 2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k - 2 * sourcePairDisconnSum G beta J {i, j} ∅ i m * currentSum G beta J {k, l} * Z - 2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m <= -2 * Z * currentSum G beta J {k, l} * (sourcePairDisconnSum G beta J {i, k} ∅ i m * sourcePairDisconnSum G beta J {k, j} ∅ k m / Z ^ 2) - 2 * Cim * (sourcePairDisconnSum G beta J {k, i} ∅ k m * sourcePairDisconnSum G beta J {i, l} ∅ i m / Z ^ 2) := by
-- proof
  apply StatMech.FrontierA.grahamEq22_correction_upper_bound_of_cutPositiveAssociation G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm hassoc


-- created on 2026-10-23
