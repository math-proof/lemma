import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SetFamily.IndependentSet
open SetFamily


namespace SetFamily

/--
[isIndependent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
lemma isIndependent_iff
  {H : Finset (Finset V)}
  {I : Finset V} :
-- imply
  IsIndependent H I ↔ ∀ e ∈ H, ¬ e ⊆ I :=
-- proof
  Iff.rfl

end SetFamily

namespace SetFamily

/--
[isIndependent_empty_hypergraph](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
lemma isIndependent_empty_hypergraph
  {I : Finset V} :
-- imply
  IsIndependent (∅ : Finset (Finset V)) I := by
-- proof
  simp [IsIndependent]

end SetFamily

namespace SetFamily

/--
[isIndependent_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
lemma isIndependent_of_subset
  {H : Finset (Finset V)}
  {I J : Finset V}
-- given
  (h : IsIndependent H I)
  (hJI : J ⊆ I) :
-- imply
  IsIndependent H J := by
-- proof
  intro e he hsub
  exact h e he (hsub.trans hJI)

end SetFamily

namespace SetFamily

/--
[isIndependent_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
lemma isIndependent_empty_iff
  {H : Finset (Finset V)} :
-- imply
  IsIndependent H ∅ ↔ ∀ e ∈ H, e.Nonempty := by
-- proof
  simp [IsIndependent, Finset.subset_empty, Finset.nonempty_iff_ne_empty]

end SetFamily

namespace SetFamily

/--
[uniform_of_isSteinerTripleSystem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
lemma uniform_of_isSteinerTripleSystem
  {H : Finset (Finset V)}
-- given
  (h : IsSteinerTripleSystem H) :
-- imply
  IsUniform H 3 :=
-- proof
  h.1

end SetFamily

namespace SetFamily

/--
[pairCover_of_isSteinerTripleSystem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
lemma pairCover_of_isSteinerTripleSystem
  {H : Finset (Finset V)}
-- given
  (h : IsSteinerTripleSystem H) :
-- imply
  ∀ u v : V, u ≠ v → ∃! e : Finset V, e ∈ H ∧ u ∈ e ∧ v ∈ e :=
-- proof
  h.2

end SetFamily

namespace SetFamily

/--
[existsUnique_mem_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
lemma existsUnique_mem_singleton
  {t : Finset V}
  {P : Finset V → Prop}
-- given
  (hP : P t) :
-- imply
  ∃! e : Finset V, e ∈ ({t} : Finset (Finset V)) ∧ P e :=
-- proof
  ⟨t, ⟨Finset.mem_singleton_self t, hP⟩,
    fun _e he => Finset.mem_singleton.mp he.1⟩

end SetFamily


-- created on 2026-10-20
-- updated on 2026-10-23
