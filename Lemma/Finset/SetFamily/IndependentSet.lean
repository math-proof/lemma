import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SetFamily.IndependentSet
open SetFamily


/--
[isIndependent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
private lemma isIndependent_iff_eq
  {H : Finset (Finset V)}
  {I : Finset V} :
-- imply
  IsIndependent H I ↔ ∀ e ∈ H, ¬ e ⊆ I := by
-- proof
  apply SetFamily.isIndependent_iff H I

/--
[isIndependent_empty_hypergraph](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
private lemma isIndependent_empty_hypergraph_eq
  {I : Finset V} :
-- imply
  IsIndependent (∅ : Finset (Finset V)) I := by
-- proof
  apply SetFamily.isIndependent_empty_hypergraph I

/--
[isIndependent_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
private lemma isIndependent_of_subset_eq
  {H : Finset (Finset V)}
  {I J : Finset V}
-- given
  (h : IsIndependent H I)
  (hJI : J ⊆ I) :
-- imply
  IsIndependent H J := by
-- proof
  apply SetFamily.isIndependent_of_subset h hJI

/--
[isIndependent_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
private lemma isIndependent_empty_iff_eq
  {H : Finset (Finset V)} :
-- imply
  IsIndependent H ∅ ↔ ∀ e ∈ H, e.Nonempty := by
-- proof
  apply SetFamily.isIndependent_empty_iff H

/--
[uniform_of_isSteinerTripleSystem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
private lemma uniform_of_isSteinerTripleSystem_eq
  {H : Finset (Finset V)}
-- given
  (h : IsSteinerTripleSystem H) :
-- imply
  IsUniform H 3 := by
-- proof
  apply SetFamily.uniform_of_isSteinerTripleSystem h

/--
[pairCover_of_isSteinerTripleSystem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
private lemma pairCover_of_isSteinerTripleSystem_eq
  {H : Finset (Finset V)}
-- given
  (h : IsSteinerTripleSystem H) :
-- imply
  ∀ u v : V, u ≠ v → ∃! e : Finset V, e ∈ H ∧ u ∈ e ∧ v ∈ e := by
-- proof
  apply SetFamily.pairCover_of_isSteinerTripleSystem h

/--
[existsUnique_mem_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean)
-/
@[path]
private lemma existsUnique_mem_singleton_eq
  {t : Finset V}
  {P : Finset V → Prop}
-- given
  (hP : P t) :
-- imply
  ∃! e : Finset V, e ∈ ({t} : Finset (Finset V)) ∧ P e := by
-- proof
  apply SetFamily.existsUnique_mem_singleton hP


-- created on 2026-10-20
