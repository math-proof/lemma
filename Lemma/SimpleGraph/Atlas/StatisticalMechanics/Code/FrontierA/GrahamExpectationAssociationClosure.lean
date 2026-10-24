import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamExpectationAssociationClosure
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamExpectation_correctedBound_of_cutPositiveAssociation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamExpectationAssociationClosure.lean)
-/
@[path]
private lemma grahamExpectation_correctedBound_of_cutPositiveAssociation_eq
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
  expectationJ G beta J {i, j, k, l} - expectationJ G beta J {i, j} * expectationJ G beta J {k, l} - expectationJ G beta J {i, k} * expectationJ G beta J {j, l} - expectationJ G beta J {i, l} * expectationJ G beta J {j, k} <= -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} * expectationJ G beta J {k, m} * expectationJ G beta J {l, m}) + -2 * ((expectationJ G beta J {i, k} - expectationJ G beta J {i, m} * expectationJ G beta J {m, k}) * (expectationJ G beta J {k, j} - expectationJ G beta J {k, m} * expectationJ G beta J {m, j}) * expectationJ G beta J {k, l}) + -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} * (expectationJ G beta J {k, i} - expectationJ G beta J {k, m} * expectationJ G beta J {m, i}) * (expectationJ G beta J {i, l} - expectationJ G beta J {i, m} * expectationJ G beta J {m, l})) := by
-- proof
  apply StatMech.FrontierA.grahamExpectation_correctedBound_of_cutPositiveAssociation G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm hassoc


-- created on 2026-10-23
