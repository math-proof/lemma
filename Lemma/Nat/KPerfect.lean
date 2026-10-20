import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.KPerfect
open Nat


/--
[IsKPerfect.pos_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KPerfect.lean)
-/
@[path]
private lemma IsKPerfect_pos_k_eq
  {k n : ℕ}
-- given
  (h : IsKPerfect k n) :
-- imply
  0 < k := by
-- proof
  apply Nat.IsKPerfect.pos_k h

/--
[isKPerfect_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KPerfect.lean)
-/
@[path]
private lemma isKPerfect_two_iff_eq
  {n : ℕ} :
-- imply
  IsKPerfect 2 n ↔ n.Perfect := by
-- proof
  apply Nat.isKPerfect_two_iff n


-- created on 2026-10-20
