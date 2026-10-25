/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexTransitive.lean -/

/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Def.Combinatorics.SimpleGraph.VertexTransitive


namespace SimpleGraph

@[simp] theorem isVertexTransitive_of_subsingleton {V : Type*} [Subsingleton V]
    (G : SimpleGraph V) : G.IsVertexTransitive := by
  intro u v
  exact ⟨SimpleGraph.Iso.refl, Subsingleton.elim _ _⟩

end SimpleGraph
