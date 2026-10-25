/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/LinearPartition.lean -/


import Structure.Combinatorics.LinearPartition
import Lemma.Finset.LinearPartition
import Mathlib.Tactic


namespace MetaMathlibExt

def graph02 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun a b => a = 0 ∧ b = 2

end MetaMathlibExt
