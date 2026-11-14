import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary
import Def.NumberTheory.RothAuxiliary.Part2
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_coeff_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P : ℤ[X])
  (n : ℕ) :
-- imply
  (P.coeff n).natAbs ≤ rothPolyL1 P := by
-- proof
  classical
  unfold rothPolyL1 rothFinsuppL1
  simp only [toFinsupp_apply]
  if hn : P.coeff n = 0 then
    simp [hn]
  else
    apply Finset.single_le_sum (fun b _ ↦ Nat.zero_le (P.coeff b).natAbs)
    simpa [support_toFinsupp] using mem_support_iff.mpr hn


-- created on 2026-10-21
-- updated on 2026-11-13
