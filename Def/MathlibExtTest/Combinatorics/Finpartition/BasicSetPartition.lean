/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Finpartition/BasicSetPartition.lean -/


import Def.Combinatorics.Finpartition.BasicSetPartition


namespace MetaMathlibExt

def groundThree : Finset ℕ := Finset.Icc 1 3

def oneBlockThree : Finpartition (Finset.Icc 1 3) :=
  Finpartition.indiscrete (by decide)

end MetaMathlibExt
