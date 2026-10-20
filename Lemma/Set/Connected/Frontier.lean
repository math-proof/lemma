import Mathlib
import sympy.Basic
import sympy.atlas.Topology.Connected.Frontier
open Set Topology


/--
[IsPreconnected.inter_frontier_nonempty_of_inter_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Connected/Frontier.lean)
-/
@[path]
private lemma IsPreconnected_inter_frontier_nonempty_of_inter_compl_eq
  [TopologicalSpace α]
  {s A : Set α}
-- given
  (hs : IsPreconnected s)
  (hA : (s ∩ A).Nonempty)
  (hAc : (s ∩ Aᶜ).Nonempty) :
-- imply
  (s ∩ frontier A).Nonempty := by
-- proof
  apply IsPreconnected.inter_frontier_nonempty_of_inter_compl hs hA hAc


-- created on 2026-10-20
