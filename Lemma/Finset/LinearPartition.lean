import Mathlib
import sympy.Basic
import Structure.Combinatorics.LinearPartition
open MetaMathlibExt


namespace MetaMathlibExt

/--
[LinearPartition.ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/LinearPartition.lean)
-/
@[path]
lemma LinearPartition.ext
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {P Q : LinearPartition G k}
-- given
  (h : P.blocks = Q.blocks) :
-- imply
  P = Q := by
-- proof
  cases P
  cases Q
  cases h
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[LinearPartition.existsUniqueBlock](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/LinearPartition.lean)
-/
@[path]
lemma LinearPartition.existsUniqueBlock
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {P : LinearPartition G k}
  {v : V} :
-- imply
  ∃! L, L ∈ P.blocks ∧ v ∈ L :=
-- proof
  P.covers v

end MetaMathlibExt

namespace MetaMathlibExt

/--
[LinearPartition.consecutive_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/LinearPartition.lean)
-/
@[path]
lemma LinearPartition.consecutive_mem
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {P : LinearPartition G k}
  {L : List V}
-- given
  (hL : L ∈ P.blocks) :
-- imply
  List.IsChain (fun a b => ¬G.Adj a b) L :=
-- proof
  P.consecutive L hL

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
