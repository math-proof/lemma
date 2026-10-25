/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ZeroDivisorGraph.lean -/

-- MathlibExtTest/RingTheory/ZeroDivisorGraph.lean
import Def.RingTheory.ZeroDivisorGraph
import Lemma.Int.ZeroDivisorGraph
import Mathlib.Data.ZMod.Basic
open ZeroDivisorGraph


/-- Vertex `2` in `ZMod 6`. -/
def v2 : Vertex (ZMod 6) :=
  ⟨2, by decide, notMem_nonZeroDivisors_iff_left.mpr ⟨3, by decide, by decide⟩⟩

/-- Vertex `3` in `ZMod 6`. -/
def v3 : Vertex (ZMod 6) :=
  ⟨3, by decide, notMem_nonZeroDivisors_iff_left.mpr ⟨2, by decide, by decide⟩⟩

/-- Vertex `4` in `ZMod 6`. -/
def v4 : Vertex (ZMod 6) :=
  ⟨4, by decide, notMem_nonZeroDivisors_iff_left.mpr ⟨3, by decide, by decide⟩⟩

/-- Vertex `4` in `ZMod 8`, a nonzero nilpotent squaring to zero. -/
def v4_8 : Vertex (ZMod 8) :=
  ⟨4, by decide, notMem_nonZeroDivisors_iff_left.mpr ⟨2, by decide, by decide⟩⟩

