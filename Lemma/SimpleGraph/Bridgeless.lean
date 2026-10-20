import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Bridgeless
open SimpleGraph


/--
[isBridgeless_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean)
-/
@[path]
private lemma isBridgeless_iff_eq
  {G : SimpleGraph V} :
-- imply
  G.IsBridgeless ↔ ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by
-- proof
  apply SimpleGraph.isBridgeless_iff

/--
[IsBridgeless.mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean)
-/
@[path]
private lemma IsBridgeless_mk_eq
  {G : SimpleGraph V}
-- given
  (h : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
-- imply
  G.IsBridgeless := by
-- proof
  apply SimpleGraph.IsBridgeless.mk h

/--
[IsBridgeless.not_isBridge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean)
-/
@[path]
private lemma IsBridgeless_not_isBridge_eq
  {G : SimpleGraph V}
  {e : Sym2 V}
-- given
  (h : G.IsBridgeless)
  (he : e ∈ G.edgeSet) :
-- imply
  ¬ G.IsBridge e := by
-- proof
  apply SimpleGraph.IsBridgeless.not_isBridge h he

/--
[isBridgeless_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean)
-/
@[path]
private lemma isBridgeless_bot_eq
  {G : SimpleGraph V} :
-- imply
  (⊥ : SimpleGraph V).IsBridgeless := by
-- proof
  apply SimpleGraph.isBridgeless_bot V


-- created on 2026-10-20
