import Mathlib
import sympy.Basic
import Def.Combinatorics.SimpleGraph.OddIndependent
open SimpleGraph


namespace SimpleGraph

/--
[IsOddIndependent.isIndepSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
lemma IsOddIndependent.isIndepSet
  {G : SimpleGraph V}
  {S : Set V}
-- given
  (h : G.IsOddIndependent S) :
-- imply
  G.IsIndepSet S :=
-- proof
  h.1

end SimpleGraph

namespace SimpleGraph

/--
[IsOddIndependent.finite_inter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
lemma IsOddIndependent.finite_inter
  {G : SimpleGraph V}
  {S : Set V}
  {v : V}
-- given
  (h : G.IsOddIndependent S)
  (hv : v ∉ S) :
-- imply
  (G.neighborSet v ∩ S).Finite :=
-- proof
  (h.2 v hv).1

end SimpleGraph

namespace SimpleGraph

/--
[IsOddIndependent.empty_or_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
lemma IsOddIndependent.empty_or_odd
  {G : SimpleGraph V}
  {S : Set V}
  {v : V}
-- given
  (h : G.IsOddIndependent S)
  (hv : v ∉ S) :
-- imply
  (G.neighborSet v ∩ S) = ∅ ∨ Odd (G.neighborSet v ∩ S).ncard :=
-- proof
  (h.2 v hv).2

end SimpleGraph

namespace SimpleGraph

/--
[isOddIndependent_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
lemma isOddIndependent_empty
  {G : SimpleGraph V} :
-- imply
  G.IsOddIndependent ∅ := by
-- proof
  refine ⟨fun u hu => absurd hu (Set.notMem_empty u), fun v _ => ?_⟩
  rw [Set.inter_empty]
  exact ⟨Set.finite_empty, Or.inl rfl⟩

end SimpleGraph

namespace SimpleGraph

/--
[isOddIndependent_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
lemma isOddIndependent_singleton
  {G : SimpleGraph V}
  {a : V} :
-- imply
  G.IsOddIndependent {a} := by
-- proof
  constructor
  · intro u hu w hw hne
    rw [Set.mem_singleton_iff] at hu hw
    exact absurd (hu.trans hw.symm) hne
  · intro v _
    have hfin : (G.neighborSet v ∩ {a}).Finite :=
      Set.Finite.subset (Set.finite_singleton a) Set.inter_subset_right
    refine ⟨hfin, ?_⟩
    by_cases ha : a ∈ G.neighborSet v
    · have heq : G.neighborSet v ∩ {a} = {a} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact hx.2
      · intro hx
        rw [hx]
        exact ⟨ha, rfl⟩
      rw [heq, Set.ncard_singleton]
      exact Or.inr odd_one
    · have hempty : G.neighborSet v ∩ {a} = ∅ := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_inter_iff, Set.mem_singleton_iff] at hx
        exact absurd (hx.2 ▸ hx.1) ha
      · intro hx
        exact absurd hx (Set.notMem_empty x)
      exact Or.inl hempty

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
