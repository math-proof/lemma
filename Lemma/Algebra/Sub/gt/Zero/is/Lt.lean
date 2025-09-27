import Lemma.Basic


@[main, comm, mp, mpr]
private lemma nat
  [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b : α} :
-- imply
  b - a > 0 ↔ a < b :=
-- proof
  -- Nat.sub_pos_iff_lt
  tsub_pos_iff_lt


/--
This lemma establishes that in an additive group with a strict order and right-strict monotonicity, the difference `b - a` being positive is equivalent to `a` being less than `b`.
It leverages the properties of additive groups and the `AddRightStrictMono` typeclass to connect the algebraic operation of subtraction with the order relation.
-/
@[main, comm, mp, mpr]
private lemma main
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α} :
-- imply
  b - a > 0 ↔ a < b :=
-- proof
  sub_pos


-- created on 2024-11-25
-- updated on 2025-04-04
