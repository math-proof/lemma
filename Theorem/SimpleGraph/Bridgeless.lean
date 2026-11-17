module

public import Mathlib
public import Def.Combinatorics.SimpleGraph.Bridgeless

public section

open SimpleGraph


namespace SimpleGraph

/--
[isBridgeless_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean)
-/
public theorem isBridgeless_iff
  {G : SimpleGraph V} :
-- imply
  G.IsBridgeless ↔ ∀ e ∈ G.edgeSet, ¬ G.IsBridge e :=
-- proof
  Iff.rfl

end SimpleGraph

namespace SimpleGraph

/--
[IsBridgeless.mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean)
-/
public theorem IsBridgeless.mk
  {G : SimpleGraph V}
-- given
  (h : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
-- imply
  G.IsBridgeless :=
-- proof
  h

end SimpleGraph

namespace SimpleGraph

/--
[IsBridgeless.not_isBridge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean)
-/
public theorem IsBridgeless.not_isBridge
  {G : SimpleGraph V}
  {e : Sym2 V}
-- given
  (h : G.IsBridgeless)
  (he : e ∈ G.edgeSet) :
-- imply
  ¬ G.IsBridge e :=
-- proof
  h e he

end SimpleGraph

namespace SimpleGraph

/--
[isBridgeless_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean)
-/
public theorem isBridgeless_bot
  :
-- imply
  (⊥ : SimpleGraph V).IsBridgeless := by
-- proof
  intro e he
  simp at he

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-26
