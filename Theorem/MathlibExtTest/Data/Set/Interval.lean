/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Data/Set/Interval.lean -/
module

public import Instance.Data.Set.Interval
public import Mathlib.Order.Interval.Finset.Nat

public section

-- Normal API use: set–interval intersections are fintypes.
noncomputable example (S : Set ℕ) (a b : ℕ) : Fintype (S ∩ Set.Icc a b : Set ℕ) :=
  inferInstance

noncomputable example (S : Set ℕ) (b : ℕ) : Fintype (S ∩ Set.Iio b : Set ℕ) :=
  inferInstance

