/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SubgraphIsomorphism.lean -/


import Def.Combinatorics.SimpleGraph.SubgraphIsomorphism
open SimpleGraph


-- Normal API use: the unique-subgraph predicate and count accept graphs.
noncomputable example (G H : SimpleGraph (Fin 4)) : Prop :=
  IsUniqueSubgraph G H

noncomputable example (H : SimpleGraph (Fin 4)) : ℕ :=
  uniqueSubgraphCount H

-- The empty graph is a unique subgraph of itself: it is the only
-- spanning subgraph isomorphic to it.
example : IsUniqueSubgraph (⊥ : SimpleGraph (Fin 4)) (⊥ : SimpleGraph (Fin 4)) := by
  refine ⟨⊥, ⟨le_rfl, ⟨RelIso.refl _⟩⟩, fun G' hG' => ?_⟩
  · obtain ⟨hle, -⟩ := hG'
    exact le_antisymm hle bot_le

