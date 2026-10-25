/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/Quadratic.lean -/


import Def.NumberTheory.DirichletCharacter.Quadratic
import Lemma.Nat.DirichletCharacter.Quadratic
import Mathlib.Tactic.NormNum.LegendreSymbol
open MetaMathlibExt


example : kroneckerSym 1 0 = 1 := by norm_num [kroneckerSym_zero]

example : kroneckerSym 1 1 = 1 := by simp [kroneckerSym_one]

example : kroneckerSym 1 2 = 1 := by norm_num [kroneckerSym_two, kroneckerAtTwo]

example : kroneckerSym 5 0 = 0 := by norm_num [kroneckerSym_zero]

example : kroneckerSym 5 1 = 1 := by simp [kroneckerSym_one]

example : kroneckerSym 5 2 = -1 := by norm_num [kroneckerSym_two, kroneckerAtTwo]

example : kroneckerSym 8 0 = 0 := by norm_num [kroneckerSym_zero]

example : kroneckerSym 8 1 = 1 := by simp [kroneckerSym_one]

example : kroneckerSym 8 2 = 0 := by norm_num [kroneckerSym_two, kroneckerAtTwo]

example : kroneckerSym 12 0 = 0 := by norm_num [kroneckerSym_zero]

example : kroneckerSym 12 1 = 1 := by simp [kroneckerSym_one]

example : kroneckerSym 12 2 = 0 := by norm_num [kroneckerSym_two, kroneckerAtTwo]

example : kroneckerSym (-4) 0 = 0 := by norm_num [kroneckerSym_zero]

example : kroneckerSym (-4) 1 = 1 := by simp [kroneckerSym_one]

example : kroneckerSym (-4) 2 = 0 := by norm_num [kroneckerSym_two, kroneckerAtTwo]

example : jacobiSym 5 2 ≠ kroneckerSym 5 2 := by
  have hk : kroneckerSym 5 2 = -1 := by norm_num [kroneckerSym_two, kroneckerAtTwo]
  have hj : jacobiSym 5 2 = 1 := by norm_num
  rw [hk, hj]
  norm_num

example : kroneckerSym 5 3 = -1 := by
  rw [kroneckerSym_prime 5 3 Nat.prime_three]
  norm_num [kroneckerAtPrime, show (3 : ℕ) ≠ 2 by decide, Nat.prime_three]

example : kroneckerSym 5 4 = 1 := by
  have hlist4 : Nat.primeFactorsList 4 = [2, 2] := by
    have hprod : [2, 2].prod = 4 := by rfl
    have hprime : ∀ p ∈ [2, 2], Nat.Prime p := by simp [Nat.prime_two]
    have hsorted1 : ([2, 2] : List ℕ).SortedLE := by decide
    have hsorted2 : (Nat.primeFactorsList 4).SortedLE :=
      Nat.primeFactorsList_sorted 4
    have hperm : ([2, 2] : List ℕ).Perm (Nat.primeFactorsList 4) :=
      Nat.primeFactorsList_unique hprod hprime
    exact (List.Perm.eq_of_sortedLE hsorted1 hsorted2 hperm).symm
  rw [kroneckerSym, ite_eq_right (by decide), hlist4]
  norm_num [kroneckerAtPrime, kroneckerAtTwo]

example : kroneckerSym 5 6 = 1 := by
  have hlist6 : Nat.primeFactorsList 6 = [2, 3] := by
    have hprod : [2, 3].prod = 6 := by rfl
    have hprime : ∀ p ∈ [2, 3], Nat.Prime p := by
      simp [Nat.prime_two, Nat.prime_three]
    have hsorted1 : ([2, 3] : List ℕ).SortedLE := by decide
    have hsorted2 : (Nat.primeFactorsList 6).SortedLE :=
      Nat.primeFactorsList_sorted 6
    have hperm : ([2, 3] : List ℕ).Perm (Nat.primeFactorsList 6) :=
      Nat.primeFactorsList_unique hprod hprime
    exact (List.Perm.eq_of_sortedLE hsorted1 hsorted2 hperm).symm
  rw [kroneckerSym, ite_eq_right (by decide), hlist6]
  norm_num [kroneckerAtPrime, kroneckerAtTwo,
    show (3 : ℕ) ≠ 2 by decide, Nat.prime_three]

example : kroneckerSym 8 3 = -1 := by
  rw [kroneckerSym_prime 8 3 Nat.prime_three]
  norm_num [kroneckerAtPrime, show (3 : ℕ) ≠ 2 by decide, Nat.prime_three]

example : kroneckerSym 12 5 = -1 := by
  rw [kroneckerSym_prime 12 5 Nat.prime_five]
  norm_num [kroneckerAtPrime, show (5 : ℕ) ≠ 2 by decide, Nat.prime_five]

example : kroneckerSym (-4) 3 = -1 := by
  rw [kroneckerSym_prime (-4) 3 Nat.prime_three]
  norm_num [kroneckerAtPrime, show (3 : ℕ) ≠ 2 by decide, Nat.prime_three]

example : IsFundamentalDiscriminant 1 := by
  left
  refine ⟨by simp, by decide⟩

example : IsFundamentalDiscriminant 5 := by
  left
  refine ⟨?_, ?_⟩
  · exact ((Int.prime_iff_natAbs_prime (k := 5)).mpr Nat.prime_five).squarefree
  · decide

example : IsFundamentalDiscriminant 8 := by
  right
  refine ⟨2, by norm_num, ?_, ?_⟩
  · exact ((Int.prime_iff_natAbs_prime (k := 2)).mpr Nat.prime_two).squarefree
  · left
    decide

example : IsFundamentalDiscriminant 12 := by
  right
  refine ⟨3, by norm_num, ?_, ?_⟩
  · exact ((Int.prime_iff_natAbs_prime (k := 3)).mpr Nat.prime_three).squarefree
  · right
    decide

example : IsFundamentalDiscriminant (-4) := by
  right
  refine ⟨-1, by norm_num, by simp, ?_⟩
  right
  decide

example : ¬ IsFundamentalDiscriminant 0 := by
  intro h
  unfold IsFundamentalDiscriminant at h
  cases h with
  | inl hleft =>
    exact not_squarefree_zero hleft.1
  | inr hright =>
    cases hright with
    | intro m hrest =>
      cases hrest with
      | intro hm hrest2 =>
        cases hrest2 with
        | intro hsq _ =>
          have hm0 : m = 0 := by omega
          subst hm0
          exact not_squarefree_zero hsq

