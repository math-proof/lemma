import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Graph.MaxFlowMinCut
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted


/--
[cutFlow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
private lemma cutFlow_eq_eq
  [Fintype V] [DecidableEq V]
  {s t : V}
  {f : V → V → ℝ}
  {S : Finset V}
-- given
  (hcons : ∀ v, v ≠ s → v ≠ t → ∑ u : V, f u v = ∑ w : V, f v w)
  (hs : s ∈ S)
  (ht : t ∉ S) :
-- imply
  flowValue s f = (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f u v) -
    (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f v u) := by
-- proof
  apply MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.cutFlow_eq s t f hcons S hs ht

/--
[flowValue_le_cutCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
private lemma flowValue_le_cutCapacity_eq
  [Fintype V] [DecidableEq V]
  {cap : V → V → ℝ}
  {s t : V}
  {f : V → V → ℝ}
  {S : Finset V}
-- given
  (hf : IsFeasibleFlow cap s t f)
  (hS : IsSTCut s t S) :
-- imply
  flowValue s f ≤ cutCapacity cap S := by
-- proof
  apply MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue_le_cutCapacity cap s t f hf S hS

/--
[max_flow_min_cut](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
private lemma max_flow_min_cut_eq
  [Fintype V] [DecidableEq V]
  {cap : V → V → ℝ}
  {s t : V}
-- given
  (hcap : ∀ u v, 0 ≤ cap u v)
  (hst : s ≠ t) :
-- imply
  ∃ f : V → V → ℝ, IsFeasibleFlow cap s t f ∧
    (∀ f' : V → V → ℝ, IsFeasibleFlow cap s t f' → flowValue s f' ≤ flowValue s f) ∧
    (∀ S : Finset V, IsSTCut s t S → flowValue s f ≤ cutCapacity cap S) ∧
    ∃ S : Finset V, IsSTCut s t S ∧ flowValue s f = cutCapacity cap S := by
-- proof
  apply MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.max_flow_min_cut cap hcap s t hst


-- created on 2026-10-20
