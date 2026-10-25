/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ZeroDivisorGraph.lean -/

-- MathlibExtTest/RingTheory/ZeroDivisorGraph.lean
import Def.RingTheory.ZeroDivisorGraph
import Lemma.Int.ZeroDivisorGraph
import Mathlib.Data.ZMod.Basic
import Def.MathlibExtTest.RingTheory.ZeroDivisorGraph
open ZeroDivisorGraph


-- `2` lifts to a vertex, characterizing vertex membership.
example : ∃ v : Vertex (ZMod 6), (v : ZMod 6) = 2 :=
  (exists_vertex_iff (ZMod 6) 2).mpr
    ⟨by decide, notMem_nonZeroDivisors_iff_left.mpr ⟨3, by decide, by decide⟩⟩

-- No vertex of `ZMod 6` coerces to the unit `1`.
example : ¬ ∃ v : Vertex (ZMod 6), (v : ZMod 6) = 1 := by
  intro h
  have hmem := ((exists_vertex_iff (ZMod 6) 1).mp h).2
  obtain ⟨s, hs0, hs⟩ := notMem_nonZeroDivisors_iff_left.mp hmem
  rw [one_mul] at hs0
  exact hs hs0

-- Adjacency `2 ~ 3` in `ZMod 6`.
example : (zeroDivisorGraph (ZMod 6)).Adj v2 v3 :=
  (adj_iff (ZMod 6)).mpr ⟨by decide, by decide⟩

-- Adjacency `3 ~ 4` in `ZMod 6`.
example : (zeroDivisorGraph (ZMod 6)).Adj v3 v4 :=
  (adj_iff (ZMod 6)).mpr ⟨by decide, by decide⟩

-- Non-adjacency `2 ~ 4` fails in `ZMod 6`.
example : ¬ (zeroDivisorGraph (ZMod 6)).Adj v2 v4 := by
  intro h
  have h2 := (adj_iff (ZMod 6)).mp h
  have hne : (v2 : ZMod 6) * (v4 : ZMod 6) ≠ 0 := by decide
  exact hne h2.2

-- Nonzero nilpotent `4` in `ZMod 8` squares to zero but has no loop.
example : (v4_8 : ZMod 8) * (v4_8 : ZMod 8) = 0 ∧
    ¬ (zeroDivisorGraph (ZMod 8)).Adj v4_8 v4_8 :=
  ⟨by decide, fun h => ((adj_iff (ZMod 8)).mp h).1 rfl⟩

