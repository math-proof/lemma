import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[kroneckerSym_mul_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/KroneckerJacobiOdd.lean)
-/
@[path]
lemma kroneckerSym_mul_of_odd
  {D : ℤ}
  {m n : ℕ}
-- given
  (hm : Odd m)
  (hn : Odd n) :
-- imply
  kroneckerSym D (m * n) = kroneckerSym D m * kroneckerSym D n := by
-- proof
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd (Nat.odd_iff.mp hm) (by decide)
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd (Nat.odd_iff.mp hn) (by decide)
  have hmn : m * n ≠ 0 := mul_ne_zero hm0 hn0
  have hperm : (m * n).primeFactorsList.Perm
    (m.primeFactorsList ++ n.primeFactorsList) :=
    Nat.perm_primeFactorsList_mul hm0 hn0
  simp only [kroneckerSym, hmn, if_false, hm0, hn0]
  have hmap : ((m * n).primeFactorsList.map (kroneckerAtPrime D)).Perm
    ((m.primeFactorsList ++ n.primeFactorsList).map (kroneckerAtPrime D)) :=
    hperm.map (kroneckerAtPrime D)
  have hperm_prod : ((m * n).primeFactorsList.map (kroneckerAtPrime D)).prod =
    ((m.primeFactorsList ++ n.primeFactorsList).map
      (kroneckerAtPrime D)).prod :=
    hmap.prod_eq
  rwa [List.map_append, List.prod_append] at hperm_prod

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kroneckerSym_eq_jacobiSym_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/KroneckerJacobiOdd.lean)
-/
@[path]
lemma kroneckerSym_eq_jacobiSym_of_odd
  {D : ℤ}
  {n : ℕ}
-- given
  (hn : Odd n) :
-- imply
  kroneckerSym D n = jacobiSym D n := by
-- proof
  have key : ∀ m : ℕ, Odd m → kroneckerSym D m = jacobiSym D m := by
    intro m
    refine Nat.recOnMul
      (motive := fun m => Odd m → kroneckerSym D m = jacobiSym D m) ?_ ?_ ?_ ?_
      m
    · intro h
      have h01 : (0 : ℕ) % 2 = 1 := Nat.odd_iff.mp h
      exact absurd h01 (by decide)
    · intro _
      have hj1 : jacobiSym D 1 = 1 := jacobiSym.one_right D
      have hk1 : kroneckerSym D 1 = 1 := kroneckerSym_one D
      rw [hj1, hk1]
    · intro p hp hodd
      have hp2 : p ≠ 2 := by rintro rfl; exact absurd (Nat.odd_iff.mp hodd) (by decide)
      exact kroneckerSym_eq_jacobiSym_of_prime_ne_two D p hp hp2
    · intro a b iha ihb h
      have hpair : Odd a ∧ Odd b := Nat.odd_mul.mp h
      have ha : Odd a := hpair.1
      have hb : Odd b := hpair.2
      have ha_ne : a ≠ 0 := by rintro rfl; exact absurd (Nat.odd_iff.mp ha) (by decide)
      have hb_ne : b ≠ 0 := by rintro rfl; exact absurd (Nat.odd_iff.mp hb) (by decide)
      rw [kroneckerSym_mul_of_odd D a b ha hb,
        jacobiSym.mul_right' D ha_ne hb_ne, iha ha, ihb hb]
  exact key n hn

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
