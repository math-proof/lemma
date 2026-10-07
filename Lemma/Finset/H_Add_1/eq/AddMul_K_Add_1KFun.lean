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
  H x (m + 1) = x 0 * K x (m + 1) + K (fun i => x (i + 1)) m := by
-- proof
  exact (EqKHShift.et.EqHAddMulKKShift x m).1.2


-- created on 2026-10-07
