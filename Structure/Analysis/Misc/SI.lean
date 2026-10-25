import Mathlib
import Theorem.Analysis.Misc.UnitsSystem.Part23
import Mathlib.Algebra.Group.MinimalAxioms


/-- The SI unit system.  In order to permit fractional dimensions, we allow dimensions to be rational; but then to maintain definitional equality of various explicit dimensions, we need to unseal the arithmetic operations on the rationals. -/
@[ext]
structure SI_dimensions where
  units_length : ℚ
  units_mass : ℚ
  units_time : ℚ
  units_current : ℚ
  units_temperature : ℚ
  units_amount : ℚ
  units_intensity : ℚ
deriving DecidableEq

