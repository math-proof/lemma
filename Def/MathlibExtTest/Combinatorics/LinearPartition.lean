/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/LinearPartition.lean -/

module

public import Structure.Combinatorics.LinearPartition
public import Theorem.Finset.LinearPartition
public import Mathlib.Tactic

@[expose] public section

namespace MetaMathlibExt

def graph02 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun a b => a = 0 ∧ b = 2

end MetaMathlibExt
