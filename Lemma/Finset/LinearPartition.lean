import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.LinearPartition
open MetaMathlibExt


/--
[LinearPartition.ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/LinearPartition.lean)
-/
@[path]
private lemma LinearPartition_ext_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {P Q : LinearPartition G k}
-- given
  (h : P.blocks = Q.blocks) :
-- imply
  P = Q := by
-- proof
  apply MetaMathlibExt.LinearPartition.ext h

/--
[LinearPartition.existsUniqueBlock](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/LinearPartition.lean)
-/
@[path]
private lemma LinearPartition_existsUniqueBlock_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {P : LinearPartition G k}
  {v : V} :
-- imply
  ∃! L, L ∈ P.blocks ∧ v ∈ L := by
-- proof
  apply MetaMathlibExt.LinearPartition.existsUniqueBlock P v

/--
[LinearPartition.consecutive_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/LinearPartition.lean)
-/
@[path]
private lemma LinearPartition_consecutive_mem_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {P : LinearPartition G k}
  {L : List V}
-- given
  (hL : L ∈ P.blocks) :
-- imply
  List.IsChain (fun a b => ¬G.Adj a b) L := by
-- proof
  apply MetaMathlibExt.LinearPartition.consecutive_mem P hL


-- created on 2026-10-20
