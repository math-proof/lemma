import Mathlib
import sympy.Basic
import Def.NumberTheory.DirichletCharacter.Quadratic
import Lemma.Nat.DirichletCharacter.Quadratic


namespace MetaMathlibExt

/--
[IsFundamentalDiscriminant.ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
lemma IsFundamentalDiscriminant.ne_zero
  {D : ℤ}
-- given
  (hD : IsFundamentalDiscriminant D) :
-- imply
  D ≠ 0 := by
-- proof
  rintro rfl
  cases hD with
  | inl hleft =>
    obtain ⟨_, hmod⟩ := hleft
    omega
  | inr hright =>
    obtain ⟨m, hm, hsqm, _⟩ := hright
    have hm0 : m = 0 := by omega
    have hdvd : (2 : ℤ) * 2 ∣ 0 := dvd_zero _
    have hsq0 : Squarefree (0 : ℤ) := by
      rwa [← hm0]
    have hunit : IsUnit (2 : ℤ) := hsq0 2 hdvd
    have h2not : ¬ IsUnit (2 : ℤ) := by
      rw [Int.isUnit_iff]
      decide
    exact h2not hunit

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsFundamentalDiscriminant.natAbs_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
lemma IsFundamentalDiscriminant.natAbs_pos
  {D : ℤ}
-- given
  (hD : IsFundamentalDiscriminant D) :
-- imply
  0 < D.natAbs := by
-- proof
  have hne : D ≠ 0 := IsFundamentalDiscriminant.ne_zero D hD
  exact Int.natAbs_pos.mpr hne

end MetaMathlibExt

namespace MetaMathlibExt

/--
[eq_one_of_natAbs_one_of_ne_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
private lemma eq_one_of_natAbs_one_of_ne_neg_one (D : ℤ)
  (hN : D.natAbs = 1) (hD : D ≠ -1) : D = 1 := by
  have h12 : D = 1 ∨ D = -1 := by omega
  cases h12 with
  | inl h => exact h
  | inr h => exact absurd h hD

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kroneckerSym_one_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
lemma kroneckerSym_one_left
  {n : ℕ} :
-- imply
  kroneckerSym 1 n = 1 := by
-- proof
  by_cases hn0 : n = 0
  · subst hn0
    rw [kroneckerSym_zero]
    simp
  · simp only [kroneckerSym, hn0, if_false]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨p, hp_mem, hpx⟩ := List.mem_map.mp hx
    have hp_prime : p.Prime :=
      Nat.prime_of_mem_primeFactorsList hp_mem
    rw [← hpx]
    by_cases hp2 : p = 2
    · subst hp2
      rw [kroneckerAtPrime_two]
      decide
    · have : Fact p.Prime := ⟨hp_prime⟩
      simp [kroneckerAtPrime, hp2, hp_prime]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kroneckerSym_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
lemma kroneckerSym_mul
  {D : ℤ}
  {m n : ℕ}
-- given
  (hD : D ≠ -1) :
-- imply
  kroneckerSym D (m * n) =
    kroneckerSym D m * kroneckerSym D n := by
-- proof
  by_cases hm : m = 0
  · subst hm
    rw [zero_mul]
    have h0 : kroneckerSym D 0 =
      if D.natAbs = 1 then 1 else 0 :=
      kroneckerSym_zero D
    by_cases hN : D.natAbs = 1
    · have hD1 : D = 1 :=
      eq_one_of_natAbs_one_of_ne_neg_one D hN hD
      subst hD1
      rw [kroneckerSym_one_left 0,
        kroneckerSym_one_left n, mul_one]
    · rw [h0, ite_eq_right hN, zero_mul]
  · by_cases hn : n = 0
    · subst hn
      rw [mul_zero]
      have h0 : kroneckerSym D 0 =
        if D.natAbs = 1 then 1 else 0 :=
        kroneckerSym_zero D
      by_cases hN : D.natAbs = 1
      · have hD1 : D = 1 :=
        eq_one_of_natAbs_one_of_ne_neg_one D hN hD
        subst hD1
        rw [kroneckerSym_one_left m,
          kroneckerSym_one_left 0, mul_one]
      · rw [h0, ite_eq_right hN, mul_zero]
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      have hperm : (m * n).primeFactorsList.Perm
        (m.primeFactorsList ++ n.primeFactorsList) :=
        Nat.perm_primeFactorsList_mul hm hn
      simp only [kroneckerSym, hmn, if_false, hm, hn]
      have hmap := hperm.map (kroneckerAtPrime D)
      have hperm_prod := hmap.prod_eq
      rwa [List.map_append, List.prod_append] at hperm_prod

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kroneckerSym_eq_jacobiSym_of_prime_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
lemma kroneckerSym_eq_jacobiSym_of_prime_ne_two
  {D : ℤ}
  {p : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2) :
-- imply
  kroneckerSym D p = jacobiSym D p := by
-- proof
  have : Fact p.Prime := ⟨hp⟩
  have hprime_eq : kroneckerSym D p = kroneckerAtPrime D p :=
    kroneckerSym_prime D p hp
  have h_at : kroneckerAtPrime D p = legendreSym p D := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym p D = jacobiSym D p :=
    jacobiSym.legendreSym.to_jacobiSym p D
  rw [hprime_eq, h_at, hleg]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
