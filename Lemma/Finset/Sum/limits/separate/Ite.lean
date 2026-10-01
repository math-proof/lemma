import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid β]
  {A B C D : Finset ℤ}
  {f g h : ℤ → ℤ → β} :
-- imply
  ∑ i ∈ C, ∑ j ∈ D, (if i ∈ A then f i j else if i ∈ B then g i j else h i j) =
    ∑ i ∈ C, (if i ∈ A then ∑ j ∈ D, f i j else if i ∈ B then ∑ j ∈ D, g i j else ∑ j ∈ D, h i j) :=
-- proof
  Finset.sum_congr rfl fun i _ => by split_ifs <;> rfl


-- created on 2020-03-17
