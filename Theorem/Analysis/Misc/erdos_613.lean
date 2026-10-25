import Mathlib
import Def.Analysis.Misc.erdos_613.Part2
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-!
Convenience simp lemmas. These are optional but help when you start proving
properties about colorings later on.
-/
@[simp] lemma adj_apex_left {v : V} : G.Adj V.apex v ↔ v ≠ V.apex := by
  cases v <;> simp [G, GAdj]

@[simp] lemma adj_apex_right {v : V} : G.Adj v V.apex ↔ v ≠ V.apex := by
  cases v <;> simp [G, GAdj]

@[simp] lemma adj_A1A1 {i j} : G.Adj (A1 i) (A1 j) ↔ i ≠ j := by
  simp [G, GAdj]

@[simp] lemma adj_A2A2 {i j} : G.Adj (A2 i) (A2 j) ↔ i ≠ j := by
  simp [G, GAdj]

@[simp] lemma adj_A1B1 {i j} : G.Adj (A1 i) (B1 j) := by
  simp [G, GAdj]

@[simp] lemma adj_B1A1 {i j} : G.Adj (B1 i) (A1 j) := by
  simp [G, GAdj]

@[simp] lemma adj_A2B2 {i j} : G.Adj (A2 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma adj_B2A2 {i j} : G.Adj (B2 j) (A2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_adj_B1B1 {j j'} : ¬ G.Adj (B1 j) (B1 j') := by
  simp [G, GAdj]

@[simp] lemma no_adj_B2B2 {j j'} : ¬ G.Adj (B2 j) (B2 j') := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A1B2 {i j} : ¬ G.Adj (A1 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2B1 {i j} : ¬ G.Adj (A2 i) (B1 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_B1A2 {i j} : ¬ G.Adj (B1 j) (A2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_B1B2 {i j} : ¬ G.Adj (B1 j) (B2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2A1 {i j} : ¬ G.Adj (A2 j) (A1 i)  := by
  simp [G, GAdj]

end PikhurkoN5
