import sympy.concrete.continuant
import sympy.Basic
import Lemma.Finset.EqKHShift.et.EqHAddMulKKShift
open Finset Continuant


@[main]
private lemma main
-- given
  (x : ℕ → ℝ)
  (m : ℕ) :
-- imply
  K x (m + 1) = H (fun i => x (i + 1)) m := by
-- proof
  exact (EqKHShift.et.EqHAddMulKKShift x m).1.1


-- created on 2026-10-07
