import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.DilatedSumsetExpansion
open Pointwise ProjectionTheory


namespace ProjectionTheory

/--
[dilated_sumset_subset_sumProductSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DilatedSumsetExpansion.lean)
-/
@[path]
lemma dilated_sumset_subset_sumProductSet
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {A : Finset (ZMod p)}
  {t : ZMod p}
-- given
  (ht : t ∈ A) :
-- imply
  A + t • A ⊆ sumProductSet A := by
-- proof
  intro x hx
  simp only [Finset.mem_add, Finset.mem_smul_finset] at hx
  obtain ⟨a, ha, y, ⟨c, hc, rfl⟩, rfl⟩ := hx
  simp only [sumProductSet, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨a, ha, t, ht, c, hc, rfl⟩
/--
Specialization of `exists_eps_dilated_sumset_expansion` to the case `D = A`:
for `|A| = p^{s_A}` with `0 < s_A < 1`, there exists `ε > 0` and some `t ∈ A`
with `|A + t·A| ≥ p^ε |A|`.
-/

end ProjectionTheory


-- created on 2026-10-23
