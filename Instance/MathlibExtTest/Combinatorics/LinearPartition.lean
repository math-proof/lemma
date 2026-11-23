/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/LinearPartition.lean -/


module

public import Structure.Combinatorics.LinearPartition
public import Theorem.Finset.LinearPartition
public import Mathlib.Tactic
public import Def.MathlibExtTest.Combinatorics.LinearPartition
@[expose] public section

namespace MetaMathlibExt

instance : DecidableRel graph02.Adj := fun a b => by
  simp only [graph02, SimpleGraph.fromRel_adj]
  infer_instance

end MetaMathlibExt
