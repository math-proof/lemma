/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean -/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
/-!
# A normal second-order number sequence

This file proves the odd-index sum-of-two-squares identity from L. Goy,
*On Identities for Normal Number Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL19/Goy/goy2.tex>.
-/


namespace MetaMathlibExt

/-- Normal second-order number sequence with nonzero integer coefficients:
`u_1 = 1`, `u_2 = a1`, `u_(n+2) = a1 * u_(n+1) + a2 * u_n`.
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`.
The Lean totalization sets `u_0 = 0`; source indices `u_1`, `u_2` are unshifted. -/
def normalSeq (a1 a2 : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a1 * normalSeq a1 a2 (n + 1) + a2 * normalSeq a1 a2 n

/-- Specialization `a1 = a`, `a2 = 1` with `a` a nonzero integer.
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`. -/
def normalSeqFib (a : ℤ) : ℕ → ℤ :=
  fun n => normalSeq a 1 n

end MetaMathlibExt
