import Mathlib.Order.Defs.LinearOrder

/-- Clamp `x` to `[a, b]` (NumPy `clip`; Lemma path `Clip`).
When `a ≤ b`, equal to `max a (min b x)` and to `(Set.projIcc a b h x : α)`. -/
def clip {α} [LinearOrder α] (x a b : α) : α := min (max x a) b
