import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry1
open scoped Nat Real BigOperators Interval Polynomial
open Filter Finset Complex Topology
open Entry1Euleriangf (chapter5DerivativeExpansion)
open MathlibExt.Analysis.Ramanujan.Part1Ch5
open Entry1


/--
[ramanujan_part1_ch5_entry1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry1.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry1_eq
  :
-- imply
  (∀ (phi : ℝ[X]) (h : ℝ),
    Polynomial.taylor h
    (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi) -
    chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi =
    Polynomial.C h * phi.derivative) ∧
    ∀ a : ℕ → ℝ,
    (∀ (phi : ℝ[X]) (h : ℝ),
    Polynomial.taylor h (chapter5DerivativeExpansion a h phi) -
    chapter5DerivativeExpansion a h phi =
    Polynomial.C h * phi.derivative) →
    a = chapter5Entry1MinusCoeff := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry1.ramanujan_part1_ch5_entry1


-- created on 2026-10-20
