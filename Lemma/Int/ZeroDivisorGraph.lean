import Mathlib
import sympy.Basic
import Def.RingTheory.ZeroDivisorGraph
open ZeroDivisorGraph


namespace ZeroDivisorGraph

/--
[exists_vertex_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ZeroDivisorGraph.lean)
-/
@[path]
lemma exists_vertex_iff
  {R : Type u} [CommRing R]
  {r : R} :
-- imply
  (∃ v : Vertex R, (v : R) = r) ↔ (r ≠ 0 ∧ r ∉ nonZeroDivisors R) := by
-- proof
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · rintro ⟨h0, hmem⟩
    exact ⟨⟨r, h0, hmem⟩, rfl⟩

end ZeroDivisorGraph

/--
[adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ZeroDivisorGraph.lean)
-/
@[path]
lemma adj_iff
  {R : Type u} [CommRing R]
  {v w : Vertex R} :
-- imply
  (zeroDivisorGraph R).Adj v w ↔ v ≠ w ∧ (v : R) * (w : R) = 0 := by
-- proof
  unfold zeroDivisorGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rw [mul_comm]; exact h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩



-- created on 2026-10-20
-- updated on 2026-10-23
