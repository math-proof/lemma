/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Recurrences/HonsbergerFibonacciP.lean -/


import Lean.Elab.Tactic.Omega
import Def.NumberTheory.Recurrences.HonsbergerFibonacciP
import Lemma.Nat.Recurrences.HonsbergerFibonacciP
open MetaMathlibExt


-- Representative values include the ordinary Fibonacci specialization.
example : fibonacciP 2 6 = 4 ∧ fibonacciP 1 10 = 55 := by
  constructor
  · have h0 : fibonacciP 2 0 = 0 := fibonacciP_zero 2
    have h1 : fibonacciP 2 1 = 1 := fibonacciP_eq_one 2 1 (by omega) (by omega)
    have h2 : fibonacciP 2 2 = 1 := fibonacciP_eq_one 2 2 (by omega) (by omega)
    have h3 : fibonacciP 2 3 = 1 := by rw [fibonacciP_rec 2 3 (by omega), h2, h0]
    have h4 : fibonacciP 2 4 = 2 := by rw [fibonacciP_rec 2 4 (by omega), h3, h1]
    have h5 : fibonacciP 2 5 = 3 := by rw [fibonacciP_rec 2 5 (by omega), h4, h2]
    rw [fibonacciP_rec 2 6 (by omega), h5, h3]
  · rw [fibonacciP_one]
    decide

-- The public characterization lemmas discharge the defining hypotheses.
example :
    fibonacciP 2 (3 + 1) * fibonacciP 2 (2 + 2) +
        ∑ j ∈ Finset.range 2,
          fibonacciP 2 (3 + 1 - (j + 1)) * fibonacciP 2 (2 + (j + 1) + 1 - 2) =
      fibonacciP 2 (3 + 2 + 2) := by
  refine honsberger_fibonacciP 2 3 2 (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_
  · exact fibonacciP_zero 2
  · intro r hr hrp
    exact fibonacciP_eq_one 2 r hr hrp
  · intro r hr
    exact fibonacciP_rec 2 r hr

