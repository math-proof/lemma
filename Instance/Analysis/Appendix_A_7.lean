import Mathlib
import Abbrev.Analysis.Appendix_A_7


/-- A coercion from integers to new integers -/
instance : Coe ℤ NewInt where
  coe n := Quot.mk make_twelve_equal_two n

