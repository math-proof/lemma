import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedNormalization
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamExpectation_preEq22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedNormalization.lean)
-/
@[path]
private lemma grahamExpectation_preEq22_eq
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
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l)
  (him : i ≠ m)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  let Z := currentSum G beta J ∅ expectationJ G beta J {i, j, k, l} - expectationJ G beta J {i, j} * expectationJ G beta J {k, l} - expectationJ G beta J {i, k} * expectationJ G beta J {j, l} - expectationJ G beta J {i, l} * expectationJ G beta J {j, k} + 2 * expectationJ G beta J {i, m} * expectationJ G beta J {j, m} * expectationJ G beta J {k, m} * expectationJ G beta J {l, m} = (2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k - 2 * sourcePairDisconnSum G beta J {i, j} ∅ i m * currentSum G beta J {k, l} * Z - 2 * StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m * sourcePairDisconnSum G beta J {k, l} ∅ k m) / Z ^ 4 := by
-- proof
  apply StatMech.FrontierA.grahamExpectation_preEq22 G beta J hij hik hil hjk hjl hkl him hjm hkm hlm


-- created on 2026-10-23
