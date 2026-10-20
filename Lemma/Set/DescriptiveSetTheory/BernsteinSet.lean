import Mathlib
import sympy.Basic
import sympy.atlas.Topology.DescriptiveSetTheory.BernsteinSet
open Set Topology
open Cardinal
open MathlibExt.Topology.DescriptiveSetTheory.BernsteinSet


/--
[bernstein_set_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/BernsteinSet.lean)
-/
@[path]
private lemma bernstein_set_exists_eq
  :
-- imply
  ∃ (B : Set ℝ), ∀ (F : Set ℝ), IsClosed F → ¬F.Countable →
    (B ∩ F).Nonempty ∧ (Set.compl B ∩ F).Nonempty := by
-- proof
  apply MathlibExt.Topology.DescriptiveSetTheory.BernsteinSet.bernstein_set_exists


-- created on 2026-10-20
