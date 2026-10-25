/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean -/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index
/-!
# Multiple-zeta and multiple-zeta-star series

This file defines multiple-zeta summands and values using strictly decreasing positive summation
variables, and multiple-zeta-star summands and values using weakly decreasing positive summation
variables. The star convention follows arXiv:2307.09867 and arXiv:2309.07569.
-/


namespace MetaMathlibExt.MultipleZeta

/-- The empty multiple-zeta index. Source: arXiv:2307.09867, empty-index convention. -/
def Index.empty : Index :=
  ⟨0, ⟨[], by simp, by simp⟩⟩

/-- The `i`th entry of a multiple-zeta index, bundled as a positive natural number. -/
def Index.entry : (index : Index) → Fin index.depth → PNat
  | ⟨_, composition⟩ => fun i =>
    ⟨composition.blocksFun i, composition.blocks_pos (composition.blocksFun_mem_blocks i)⟩

end MetaMathlibExt.MultipleZeta
