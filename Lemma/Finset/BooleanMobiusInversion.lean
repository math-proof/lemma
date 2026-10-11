import Mathlib
import sympy.Basic
import sympy.concrete.BooleanMobiusInversion
open scoped BigOperators


/--
[BooleanMobiusInversion](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/BooleanMobiusInversion.lean)
-/
@[path]
private lemma alternating_sum_superset_eq_iverson_a_eq
  [DecidableEq α]
  {P Q : Finset α}
-- given
  (hPQ : P ⊆ Q) :
-- imply
  ∑ I ∈ Q.powerset.filter (fun I => P ⊆ I), (-1 : ℤ) ^ I.card =
    (-1) ^ P.card * if P = Q then 1 else 0 := by
-- proof
  apply BooleanMobius.alternatingSum_superset_eq_iverson_a hPQ

/--
[BooleanMobiusInversion](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/BooleanMobiusInversion.lean)
-/
@[path]
private lemma alternating_sum_superset_eq_iverson_b_eq
  [DecidableEq α]
  {P Q : Finset α}
-- given
  (hPQ : P ⊆ Q) :
-- imply
  ∑ I ∈ Q.powerset.filter (fun I => P ⊆ I), (-1 : ℤ) ^ (Q \ I).card =
    if P = Q then 1 else 0 := by
-- proof
  apply BooleanMobius.alternatingSum_superset_eq_iverson_b hPQ

/--
[BooleanMobiusInversion](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/BooleanMobiusInversion.lean)
-/
@[path]
private lemma boolean_mobius_inversion_is
  [DecidableEq α] [AddCommGroup A]
  {S : Finset α}
-- given
  (a b : Finset α → A)
  (hab : ∀ I ⊆ S, b I = ∑ J ∈ I.powerset, a J) :
-- imply
  ∀ I ⊆ S, a I = ∑ J ∈ I.powerset, (-1 : ℤ) ^ (I \ J).card • b J := by
-- proof
  apply BooleanMobius.booleanMobiusInversion a b hab

/--
[BooleanMobiusInversion](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/BooleanMobiusInversion.lean)
-/
@[path]
private lemma boolean_mobius_inversion'_is
  [DecidableEq α] [AddCommGroup A] [Module ℤ A]
  {S : Finset α}
-- given
  (a b : Finset α → A)
  (hab : ∀ I ⊆ S, b I = ∑ J ∈ I.powerset, a J) :
-- imply
  ∀ I ⊆ S, a I = ∑ J ∈ I.powerset, ((-1 : ℤ) ^ (I \ J).card) • b J := by
-- proof
  apply BooleanMobius.booleanMobiusInversion' a b hab


-- created on 2026-10-11
