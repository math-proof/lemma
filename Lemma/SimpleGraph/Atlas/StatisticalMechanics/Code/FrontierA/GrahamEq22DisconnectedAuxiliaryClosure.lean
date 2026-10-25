import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamEq22DisconnectedAuxiliaryClosure
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamEq22_correction_upper_bound_of_auxiliary_nonreach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamEq22DisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma grahamEq22_correction_upper_bound_of_auxiliary_nonreach_eq
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
  (hkm_disc : ¬ G.Reachable k m)
  (him_disc : ¬ G.Reachable i m) :
-- imply
  let Z := currentSum G beta J ∅ let Cim := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m 2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k - 2 * sourcePairDisconnSum G beta J {i, j} ∅ i m * currentSum G beta J {k, l} * Z - 2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m <= -2 * Z * currentSum G beta J {k, l} * (sourcePairDisconnSum G beta J {i, k} ∅ i m * sourcePairDisconnSum G beta J {k, j} ∅ k m / Z ^ 2) - 2 * Cim * (sourcePairDisconnSum G beta J {k, i} ∅ k m * sourcePairDisconnSum G beta J {i, l} ∅ i m / Z ^ 2) := by
-- proof
  apply StatMech.FrontierA.grahamEq22_correction_upper_bound_of_auxiliary_nonreach G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm hkm_disc him_disc

/--
[grahamExpectation_correctedBound_of_eq22_correction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamEq22DisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma grahamExpectation_correctedBound_of_eq22_correction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
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
  (hcur : let Z := currentSum G beta J ∅ let Cim := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m 2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k - 2 * sourcePairDisconnSum G beta J {i, j} ∅ i m * currentSum G beta J {k, l} * Z - 2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m <= -2 * Z * currentSum G beta J {k, l} * (sourcePairDisconnSum G beta J {i, k} ∅ i m * sourcePairDisconnSum G beta J {k, j} ∅ k m / Z ^ 2) - 2 * Cim * (sourcePairDisconnSum G beta J {k, i} ∅ k m * sourcePairDisconnSum G beta J {i, l} ∅ i m / Z ^ 2)) :
-- imply
  expectationJ G beta J {i, j, k, l} - expectationJ G beta J {i, j} * expectationJ G beta J {k, l} - expectationJ G beta J {i, k} * expectationJ G beta J {j, l} - expectationJ G beta J {i, l} * expectationJ G beta J {j, k} <= -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} * expectationJ G beta J {k, m} * expectationJ G beta J {l, m}) + -2 * ((expectationJ G beta J {i, k} - expectationJ G beta J {i, m} * expectationJ G beta J {m, k}) * (expectationJ G beta J {k, j} - expectationJ G beta J {k, m} * expectationJ G beta J {m, j}) * expectationJ G beta J {k, l}) + -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} * (expectationJ G beta J {k, i} - expectationJ G beta J {k, m} * expectationJ G beta J {m, i}) * (expectationJ G beta J {i, l} - expectationJ G beta J {i, m} * expectationJ G beta J {m, l})) := by
-- proof
  apply StatMech.FrontierA.grahamExpectation_correctedBound_of_eq22_correction G beta J hij hik hil him hjk hjl hjm hkl hkm hlm hcur

/--
[grahamExpectation_correctedBound_of_auxiliary_nonreach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamEq22DisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma grahamExpectation_correctedBound_of_auxiliary_nonreach_eq
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
  (hkm_disc : ¬ G.Reachable k m)
  (him_disc : ¬ G.Reachable i m) :
-- imply
  expectationJ G beta J {i, j, k, l} - expectationJ G beta J {i, j} * expectationJ G beta J {k, l} - expectationJ G beta J {i, k} * expectationJ G beta J {j, l} - expectationJ G beta J {i, l} * expectationJ G beta J {j, k} <= -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} * expectationJ G beta J {k, m} * expectationJ G beta J {l, m}) + -2 * ((expectationJ G beta J {i, k} - expectationJ G beta J {i, m} * expectationJ G beta J {m, k}) * (expectationJ G beta J {k, j} - expectationJ G beta J {k, m} * expectationJ G beta J {m, j}) * expectationJ G beta J {k, l}) + -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} * (expectationJ G beta J {k, i} - expectationJ G beta J {k, m} * expectationJ G beta J {m, i}) * (expectationJ G beta J {i, l} - expectationJ G beta J {i, m} * expectationJ G beta J {m, l})) := by
-- proof
  apply StatMech.FrontierA.grahamExpectation_correctedBound_of_auxiliary_nonreach G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm hkm_disc him_disc


-- created on 2026-10-23
