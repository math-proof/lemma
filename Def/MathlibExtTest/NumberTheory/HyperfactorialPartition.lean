/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HyperfactorialPartition.lean -/


import Structure.NumberTheory.HyperfactorialPartition


namespace MetaMathlibExt

def hyperfactorialPartitionZero : HyperfactorialPartition 0 where
  k := 0
  digits := Fin.elim0
  bound := by intro i; exact Fin.elim0 i
  normalized := by
    intro h
    exact (Nat.not_lt_zero 0 h).elim
  value := by decide

def hyperfactorialPartitionOne : HyperfactorialPartition 1 where
  k := 1
  digits := fun _ => 1
  bound := by decide
  normalized := by simp [HyperfactorialDigitsNormalized]
  value := by decide

def hyperfactorialPartitionTwo : HyperfactorialPartition 2 where
  k := 1
  digits := fun _ => 2
  bound := by decide
  normalized := by simp [HyperfactorialDigitsNormalized]
  value := by decide

end MetaMathlibExt
