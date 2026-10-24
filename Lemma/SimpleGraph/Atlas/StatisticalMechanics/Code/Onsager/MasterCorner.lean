import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.MasterCorner
open StatMech StatMech.Onsager StatMech.Onsager.MasterCorner


/--
[cornerWeight_master](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MasterCorner.lean)
-/
@[path]
private lemma cornerWeight_master_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = (if leftParity d 0 = 1 then (1 : ℤ) else -1) * (if d (i + 1) - d i = 1 then 1 else 0) := by
-- proof
  apply StatMech.Onsager.MasterCorner.cornerWeight_master d hclosed hsimple hn hreflexfree i

/--
[cornerDiff_eq_weight_mul_cc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MasterCorner.lean)
-/
@[path]
private lemma cornerDiff_eq_weight_mul_cc_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cornerDiff (interiorCells d hclosed) = (if leftParity d 0 = 1 then (1 : ℤ) else -1) * (cc d : ℤ) := by
-- proof
  apply StatMech.Onsager.MasterCorner.cornerDiff_eq_weight_mul_cc d hclosed hsimple hn hreflexfree

/--
[cc_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MasterCorner.lean)
-/
@[path]
private lemma cc_eq_four_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hpinch : pinchCount (interiorCells d hclosed) = 0)
  (hchi : eulerChar (interiorCells d hclosed) = 1) :
-- imply
  cc d = 4 := by
-- proof
  apply StatMech.Onsager.MasterCorner.cc_eq_four d hclosed hsimple hn hreflexfree hpinch hchi


-- created on 2026-10-23
