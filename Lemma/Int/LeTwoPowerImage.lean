import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.GroupTheory.TwoPowerRank.Part2
open AbelianGroup


namespace AbelianGroup

/--
[twoPowerImage_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean)
-/
@[path]
private lemma twoPowerImage_succ_le
  [AddCommGroup A]
  {k : ℕ} :
-- imply
  twoPowerImage A (k + 1) ≤ twoPowerImage A k := by
-- proof
  rintro x ⟨a, rfl⟩
  refine ⟨2 • a, ?_⟩
  simp only [LinearMap.lsmul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  rw [smul_smul]
  norm_num [pow_succ, mul_comm]

end AbelianGroup


-- created on 2026-10-20
-- updated on 2026-10-26
