import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Circumference
open SimpleGraph


/--
[mem_cycleLengths](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Circumference.lean)
-/
@[path]
private lemma mem_cycleLengths_eq
  {G : SimpleGraph α}
  {m : ℕ} :
-- imply
  m ∈ G.cycleLengths ↔ ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m := by
-- proof
  apply SimpleGraph.mem_cycleLengths

/--
[mem_oddCycleLengths](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Circumference.lean)
-/
@[path]
private lemma mem_oddCycleLengths_eq
  {G : SimpleGraph α}
  {m : ℕ} :
-- imply
  m ∈ G.oddCycleLengths ↔ m ∈ G.cycleLengths ∧ Odd m := by
-- proof
  apply SimpleGraph.mem_oddCycleLengths


-- created on 2026-10-20
