/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ParkingFunction.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi

namespace MetaMathlibExt

/-! # Parking functions

This file provides the threshold formulation of partial and ordinary parking
functions. It gives a direct finite decision procedure. In the ordinary case,
the predicate is equivalent to the usual formulation in which the sorted
preferences lie below the identity; for `s` cars and `t` spots, the analogous
partial sorted bound is shifted to `bᵢ ≤ t - s + i`.
-/

/-- A partial parking function with `s` cars and `t` spots: for every spot
`k`, at most `t - k` cars prefer `k` or a later spot. -/
def IsPartialParkingFunction (s t : ℕ) (f : Fin s → Fin t) : Prop :=
  ∀ k : Fin t,
    (Finset.univ.filter (fun i => k ≤ f i)).card ≤ t - (k : ℕ)

/-- An ordinary parking function is a partial parking function with equally
many cars and spots. -/
def IsParkingFunction (n : ℕ) (f : Fin n → Fin n) : Prop :=
  IsPartialParkingFunction n n f

instance (s t : ℕ) (f : Fin s → Fin t) :
    Decidable (IsPartialParkingFunction s t f) := by
  unfold IsPartialParkingFunction
  infer_instance

instance (n : ℕ) (f : Fin n → Fin n) : Decidable (IsParkingFunction n f) := by
  unfold IsParkingFunction
  infer_instance
end MetaMathlibExt
