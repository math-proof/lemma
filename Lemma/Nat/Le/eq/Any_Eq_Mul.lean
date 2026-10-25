import Mathlib
import sympy.Basic
import Def.Analysis.Section_8_5.Part4
open Chapter8
open Chapter8.PNat


/--
[PNat.divOrder_exists](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  :
-- imply
  ∃ (h₀ : PartialOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) :=
-- proof
  Chapter8.PNat.divOrder_exists


-- created on 2026-10-22
