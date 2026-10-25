/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/LinearPartition.lean -/


import Structure.Combinatorics.LinearPartition
import Lemma.Finset.LinearPartition
import Mathlib.Tactic
import Def.MathlibExtTest.Combinatorics.LinearPartition


namespace MetaMathlibExt

instance : DecidableRel graph02.Adj := fun a b => by
  simp only [graph02, SimpleGraph.fromRel_adj]
  infer_instance

end MetaMathlibExt
