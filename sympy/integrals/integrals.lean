import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


/-- dummy base type, so that `ℒ` can be raised to an exponent like in textbooks;
the name refers to the Lebesgue spaces `Lᵖ` -/
inductive LSpace | mk


/-- the base of the textbook `ℒ¹`, `ℒᵖ` notation -/
def ℒ : LSpace := .mk


/--
`ℒ ^ p a b` is the set of functions integrable on the (unordered) interval between `a` and `b`;
currently only `p = 1` is meaningful, and `f ∈ ℒ¹ a b` unfolds to
`IntervalIntegrable f MeasureTheory.volume a b` by definition.
Similar to `sympy.integrals.integrals.Integral`, textbooks write `f ∈ ℒ¹(a, b)`.
-/
instance : HPow LSpace ℕ (ℝ → ℝ → Set (ℝ → ℝ)) :=
  ⟨fun _ _ a b => {f | IntervalIntegrable f MeasureTheory.volume a b}⟩


-- application binds tighter than `^`, so parentheses are required around `ℒ ^ 1`;
-- the atomic notation hides them, giving `f ∈ ℒ¹ a b`.
-- The type ascription is required: without an expected type, Lean's generic
-- `instHPow` (result = base type) is tried and fails before our instance is found.
notation "ℒ¹" => (ℒ ^ 1 : ℝ → ℝ → Set (ℝ → ℝ))
