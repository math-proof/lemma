module

public import Mathlib
public import Instance.Analysis.Appendix_A_7

public section

theorem NewInt.is_coe (N:NewInt) : ∃ n:ℤ, N = (n:NewInt) := by
  apply Quot.ind (q := N); intro n
  use n

