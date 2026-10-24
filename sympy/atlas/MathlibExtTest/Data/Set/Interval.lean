/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Data/Set/Interval.lean -/


import sympy.atlas.Data.Set.Interval
import Mathlib.Order.Interval.Finset.Nat


-- Normal API use: set–interval intersections are fintypes.
noncomputable example (S : Set ℕ) (a b : ℕ) : Fintype (S ∩ Set.Icc a b : Set ℕ) :=
  inferInstance

noncomputable example (S : Set ℕ) (b : ℕ) : Fintype (S ∩ Set.Iio b : Set ℕ) :=
  inferInstance
