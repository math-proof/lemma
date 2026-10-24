import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.QuadraticReciprocityBridgeFour
import Lemma.Nat.DirichletCharacter.QuadraticReciprocityBridgeFour
open MetaMathlibExt


/--
[chi7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma chi7 : (ZMod.χ₄ 7 : ℤ) = -1 :=
  ZMod.χ₄_nat_three_mod_four (by decide)

/--
[chi5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma chi5 : (ZMod.χ₄ 5 : ℤ) = 1 :=
  ZMod.χ₄_nat_one_mod_four (by decide)

/--
[chi3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma chi3 : (ZMod.χ₄ 3 : ℤ) = -1 :=
  ZMod.χ₄_nat_three_mod_four (by decide)

/--
[chi9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma chi9 : (ZMod.χ₄ 9 : ℤ) = 1 :=
  ZMod.χ₄_nat_one_mod_four (by decide)

/--
[jacMain3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacMain3_7 : jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs = 1 := by
norm_num

/--
[kronMain3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronMain3_7 : kroneckerSym (4 * (3 : ℤ)) 7 = -1 := by
  have hp : Nat.Prime 7 := by norm_num
  have hp2 : 7 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 7) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (3 : ℤ)) 7 = kroneckerAtPrime (4 * (3 : ℤ)) 7 :=
    kroneckerSym_prime (4 * (3 : ℤ)) 7 hp
  have hat : kroneckerAtPrime (4 * (3 : ℤ)) 7 = legendreSym 7 (4 * (3 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 7 (4 * (3 : ℤ)) = jacobiSym (4 * (3 : ℤ)) 7 :=
    jacobiSym.legendreSym.to_jacobiSym 7 (4 * (3 : ℤ))
  have hjac : jacobiSym (4 * (3 : ℤ)) 7 = -1 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[agreeMain3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeMain3_7 :
  (ZMod.χ₄ 7 : ℤ) * jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs =
    kroneckerSym (4 * (3 : ℤ)) 7 := by
  rw [chi7, jacMain3_7, kronMain3_7]
  decide

/--
[uncorrMain3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma uncorrMain3_7 :
  jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs ≠ kroneckerSym (4 * (3 : ℤ)) 7 := by
  rw [jacMain3_7, kronMain3_7]
  decide

/--
[bridgeMain3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeMain3_7 :
  (ZMod.χ₄ 7 : ℤ) * jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs =
    kroneckerSym (4 * (3 : ℤ)) 7 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    3 7 (by decide) (by decide)

/--
[jacMainNeg5_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacMainNeg5_7 : jacobiSym ((7 : ℕ) : ℤ) (-5 : ℤ).natAbs = -1 := by
norm_num

/--
[kronMainNeg5_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronMainNeg5_7 : kroneckerSym (4 * (-5 : ℤ)) 7 = 1 := by
  have hp : Nat.Prime 7 := by norm_num
  have hp2 : 7 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 7) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (-5 : ℤ)) 7 = kroneckerAtPrime (4 * (-5 : ℤ)) 7 :=
    kroneckerSym_prime (4 * (-5 : ℤ)) 7 hp
  have hat : kroneckerAtPrime (4 * (-5 : ℤ)) 7 = legendreSym 7 (4 * (-5 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 7 (4 * (-5 : ℤ)) = jacobiSym (4 * (-5 : ℤ)) 7 :=
    jacobiSym.legendreSym.to_jacobiSym 7 (4 * (-5 : ℤ))
  have hjac : jacobiSym (4 * (-5 : ℤ)) 7 = 1 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[agreeMainNeg5_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeMainNeg5_7 :
  (ZMod.χ₄ 7 : ℤ) * jacobiSym ((7 : ℕ) : ℤ) (-5 : ℤ).natAbs =
    kroneckerSym (4 * (-5 : ℤ)) 7 := by
  rw [chi7, jacMainNeg5_7, kronMainNeg5_7]
  decide

/--
[uncorrMainNeg5_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma uncorrMainNeg5_7 :
  jacobiSym ((7 : ℕ) : ℤ) (-5 : ℤ).natAbs ≠ kroneckerSym (4 * (-5 : ℤ)) 7 := by
  rw [jacMainNeg5_7, kronMainNeg5_7]
  decide

/--
[bridgeMainNeg5_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeMainNeg5_7 :
  (ZMod.χ₄ 7 : ℤ) * jacobiSym ((7 : ℕ) : ℤ) (-5 : ℤ).natAbs =
    kroneckerSym (4 * (-5 : ℤ)) 7 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    (-5) 7 (by decide) (by decide)

/--
[jacMain7_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacMain7_5 : jacobiSym ((5 : ℕ) : ℤ) (7 : ℤ).natAbs = -1 := by
norm_num

/--
[kronMain7_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronMain7_5 : kroneckerSym (4 * (7 : ℤ)) 5 = -1 := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : 5 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 5) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (7 : ℤ)) 5 = kroneckerAtPrime (4 * (7 : ℤ)) 5 :=
    kroneckerSym_prime (4 * (7 : ℤ)) 5 hp
  have hat : kroneckerAtPrime (4 * (7 : ℤ)) 5 = legendreSym 5 (4 * (7 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 5 (4 * (7 : ℤ)) = jacobiSym (4 * (7 : ℤ)) 5 :=
    jacobiSym.legendreSym.to_jacobiSym 5 (4 * (7 : ℤ))
  have hjac : jacobiSym (4 * (7 : ℤ)) 5 = -1 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[agreeMain7_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeMain7_5 :
  (ZMod.χ₄ 5 : ℤ) * jacobiSym ((5 : ℕ) : ℤ) (7 : ℤ).natAbs =
    kroneckerSym (4 * (7 : ℤ)) 5 := by
  rw [chi5, jacMain7_5, kronMain7_5]
  decide

/--
[bridgeMain7_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeMain7_5 :
  (ZMod.χ₄ 5 : ℤ) * jacobiSym ((5 : ℕ) : ℤ) (7 : ℤ).natAbs =
    kroneckerSym (4 * (7 : ℤ)) 5 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    7 5 (by decide) (by decide)

/--
[jacOut5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacOut5_3 : jacobiSym ((3 : ℕ) : ℤ) (5 : ℤ).natAbs = -1 := by
norm_num

/--
[kronOut5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronOut5_3 : kroneckerSym (4 * (5 : ℤ)) 3 = -1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (5 : ℤ)) 3 = kroneckerAtPrime (4 * (5 : ℤ)) 3 :=
    kroneckerSym_prime (4 * (5 : ℤ)) 3 hp
  have hat : kroneckerAtPrime (4 * (5 : ℤ)) 3 = legendreSym 3 (4 * (5 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (4 * (5 : ℤ)) = jacobiSym (4 * (5 : ℤ)) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (4 * (5 : ℤ))
  have hjac : jacobiSym (4 * (5 : ℤ)) 3 = -1 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[disagreeOut5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma disagreeOut5_3 :
  (ZMod.χ₄ 3 : ℤ) * jacobiSym ((3 : ℕ) : ℤ) (5 : ℤ).natAbs ≠
    kroneckerSym (4 * (5 : ℤ)) 3 := by
  rw [chi3, jacOut5_3, kronOut5_3]
  decide

/--
[kronBase12_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronBase12_3 : kroneckerSym (4 * (3 : ℤ)) 3 = 0 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (3 : ℤ)) 3 = kroneckerAtPrime (4 * (3 : ℤ)) 3 :=
    kroneckerSym_prime (4 * (3 : ℤ)) 3 hp
  have hat : kroneckerAtPrime (4 * (3 : ℤ)) 3 = legendreSym 3 (4 * (3 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (4 * (3 : ℤ)) = jacobiSym (4 * (3 : ℤ)) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (4 * (3 : ℤ))
  have hjac : jacobiSym (4 * (3 : ℤ)) 3 = 0 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[kronComp3_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronComp3_9 : kroneckerSym (4 * (3 : ℤ)) 9 = 0 := by
  have h9 : (9 : ℕ) = 3 * 3 := by norm_num
  have hmul : kroneckerSym (4 * (3 : ℤ)) (3 * 3) =
    kroneckerSym (4 * (3 : ℤ)) 3 * kroneckerSym (4 * (3 : ℤ)) 3 :=
    kroneckerSym_mul (4 * (3 : ℤ)) (by decide) 3 3
  rw [h9, hmul, kronBase12_3]
  decide

/--
[jacComp3_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacComp3_9 : jacobiSym ((9 : ℕ) : ℤ) (3 : ℤ).natAbs = 0 := by
norm_num

/--
[agreeComp3_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeComp3_9 :
  (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (3 : ℤ).natAbs =
    kroneckerSym (4 * (3 : ℤ)) 9 := by
  rw [chi9, jacComp3_9, kronComp3_9]
  decide

/--
[bridgeComp3_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeComp3_9 :
  (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (3 : ℤ).natAbs =
    kroneckerSym (4 * (3 : ℤ)) 9 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    3 9 (by decide) (by decide)

/--
[kronBase28_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronBase28_3 : kroneckerSym (4 * (7 : ℤ)) 3 = 1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (7 : ℤ)) 3 = kroneckerAtPrime (4 * (7 : ℤ)) 3 :=
    kroneckerSym_prime (4 * (7 : ℤ)) 3 hp
  have hat : kroneckerAtPrime (4 * (7 : ℤ)) 3 = legendreSym 3 (4 * (7 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (4 * (7 : ℤ)) = jacobiSym (4 * (7 : ℤ)) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (4 * (7 : ℤ))
  have hjac : jacobiSym (4 * (7 : ℤ)) 3 = 1 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[kronComp7_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronComp7_9 : kroneckerSym (4 * (7 : ℤ)) 9 = 1 := by
  have h9 : (9 : ℕ) = 3 * 3 := by norm_num
  have hmul : kroneckerSym (4 * (7 : ℤ)) (3 * 3) =
    kroneckerSym (4 * (7 : ℤ)) 3 * kroneckerSym (4 * (7 : ℤ)) 3 :=
    kroneckerSym_mul (4 * (7 : ℤ)) (by decide) 3 3
  rw [h9, hmul, kronBase28_3]
  decide

/--
[jacComp7_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacComp7_9 : jacobiSym ((9 : ℕ) : ℤ) (7 : ℤ).natAbs = 1 := by
norm_num

/--
[agreeComp7_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeComp7_9 :
  (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (7 : ℤ).natAbs =
    kroneckerSym (4 * (7 : ℤ)) 9 := by
  rw [chi9, jacComp7_9, kronComp7_9]
  decide

/--
[bridgeComp7_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeComp7_9 :
  (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (7 : ℤ).natAbs =
    kroneckerSym (4 * (7 : ℤ)) 9 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    7 9 (by decide) (by decide)

/--
[kronBaseNeg20_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronBaseNeg20_3 : kroneckerSym (4 * (-5 : ℤ)) 3 = 1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (-5 : ℤ)) 3 = kroneckerAtPrime (4 * (-5 : ℤ)) 3 :=
    kroneckerSym_prime (4 * (-5 : ℤ)) 3 hp
  have hat : kroneckerAtPrime (4 * (-5 : ℤ)) 3 = legendreSym 3 (4 * (-5 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (4 * (-5 : ℤ)) = jacobiSym (4 * (-5 : ℤ)) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (4 * (-5 : ℤ))
  have hjac : jacobiSym (4 * (-5 : ℤ)) 3 = 1 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[kronCompNeg5_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronCompNeg5_9 : kroneckerSym (4 * (-5 : ℤ)) 9 = 1 := by
  have h9 : (9 : ℕ) = 3 * 3 := by norm_num
  have hmul : kroneckerSym (4 * (-5 : ℤ)) (3 * 3) =
    kroneckerSym (4 * (-5 : ℤ)) 3 * kroneckerSym (4 * (-5 : ℤ)) 3 :=
    kroneckerSym_mul (4 * (-5 : ℤ)) (by decide) 3 3
  rw [h9, hmul, kronBaseNeg20_3]
  decide

/--
[jacCompNeg5_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacCompNeg5_9 : jacobiSym ((9 : ℕ) : ℤ) (-5 : ℤ).natAbs = 1 := by
norm_num

/--
[agreeCompNeg5_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeCompNeg5_9 :
  (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (-5 : ℤ).natAbs =
    kroneckerSym (4 * (-5 : ℤ)) 9 := by
  rw [chi9, jacCompNeg5_9, kronCompNeg5_9]
  decide

/--
[bridgeCompNeg5_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeCompNeg5_9 :
  (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (-5 : ℤ).natAbs =
    kroneckerSym (4 * (-5 : ℤ)) 9 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    (-5) 9 (by decide) (by decide)

/--
[chi15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma chi15 : (ZMod.χ₄ 15 : ℤ) = -1 :=
  ZMod.χ₄_nat_three_mod_four (by decide)

/--
[jacComp7_15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacComp7_15 : jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs = 1 := by
norm_num

/--
[kronComp28_15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronComp28_15 : kroneckerSym (4 * (7 : ℤ)) 15 = -1 := by
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  have hmul : kroneckerSym (4 * (7 : ℤ)) (3 * 5) =
    kroneckerSym (4 * (7 : ℤ)) 3 * kroneckerSym (4 * (7 : ℤ)) 5 :=
    kroneckerSym_mul (4 * (7 : ℤ)) (by decide) 3 5
  rw [h15, hmul, kronBase28_3, kronMain7_5]
  decide

/--
[agreeComp7_15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeComp7_15 :
  (ZMod.χ₄ 15 : ℤ) * jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs =
    kroneckerSym (4 * (7 : ℤ)) 15 := by
  rw [chi15, jacComp7_15, kronComp28_15]
  decide

/--
[uncorrComp7_15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma uncorrComp7_15 :
  jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs ≠ kroneckerSym (4 * (7 : ℤ)) 15 := by
  rw [jacComp7_15, kronComp28_15]
  decide

/--
[bridgeComp7_15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeComp7_15 :
  (ZMod.χ₄ 15 : ℤ) * jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs =
    kroneckerSym (4 * (7 : ℤ)) 15 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    7 15 (by decide) (by decide)

/--
[jac4_3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jac4_3_7 : jacobiSym (4 * (3 : ℤ)) 7 = -1 := by
norm_num

/--
[jacm_3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacm_3_7 : jacobiSym (3 : ℤ) 7 = -1 := by
norm_num

/--
[jac2_3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jac2_3_7 : jacobiSym (2 * (3 : ℤ)) 7 = -1 := by
norm_num

/--
[chi8_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma chi8_7 : (ZMod.χ₈ 7 : ℤ) = 1 := by
  have hat : jacobiSym (2 : ℤ) 7 = (ZMod.χ₈ 7 : ℤ) := jacobiSym.at_two (by decide)
  have hjac : jacobiSym (2 : ℤ) 7 = 1 := by norm_num
  rwa [← hat]

/--
[agreeRed4_3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeRed4_3_7 : jacobiSym (4 * (3 : ℤ)) 7 = jacobiSym (3 : ℤ) 7 := by
  rw [jac4_3_7, jacm_3_7]

/--
[agreeRed2_3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeRed2_3_7 :
  jacobiSym (2 * (3 : ℤ)) 7 = (ZMod.χ₈ 7 : ℤ) * jacobiSym (3 : ℤ) 7 := by
  rw [jac2_3_7, chi8_7, jacm_3_7]
  decide

/--
[bridgeRed4_3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeRed4_3_7 : jacobiSym (4 * (3 : ℤ)) 7 = jacobiSym (3 : ℤ) 7 :=
  jacobiSym_four_mul_of_odd _ _ (by decide)

/--
[bridgeRed2_3_7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeRed2_3_7 :
  jacobiSym (2 * (3 : ℤ)) 7 = (ZMod.χ₈ 7 : ℤ) * jacobiSym (3 : ℤ) 7 :=
  jacobiSym_two_mul_of_odd _ _ (by decide)

/--
[jac4_5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jac4_5_3 : jacobiSym (4 * (5 : ℤ)) 3 = -1 := by
norm_num

/--
[jacm_5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacm_5_3 : jacobiSym (5 : ℤ) 3 = -1 := by
norm_num

/--
[jac2_5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jac2_5_3 : jacobiSym (2 * (5 : ℤ)) 3 = 1 := by
norm_num

/--
[chi8_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma chi8_3 : (ZMod.χ₈ 3 : ℤ) = -1 := by
  have hat : jacobiSym (2 : ℤ) 3 = (ZMod.χ₈ 3 : ℤ) := jacobiSym.at_two (by decide)
  have hjac : jacobiSym (2 : ℤ) 3 = -1 := by norm_num
  rwa [← hat]

/--
[agreeRed4_5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeRed4_5_3 : jacobiSym (4 * (5 : ℤ)) 3 = jacobiSym (5 : ℤ) 3 := by
  rw [jac4_5_3, jacm_5_3]

/--
[agreeRed2_5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeRed2_5_3 :
  jacobiSym (2 * (5 : ℤ)) 3 = (ZMod.χ₈ 3 : ℤ) * jacobiSym (5 : ℤ) 3 := by
  rw [jac2_5_3, chi8_3, jacm_5_3]
  decide

/--
[bridgeRed4_5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeRed4_5_3 : jacobiSym (4 * (5 : ℤ)) 3 = jacobiSym (5 : ℤ) 3 :=
  jacobiSym_four_mul_of_odd _ _ (by decide)

/--
[bridgeRed2_5_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeRed2_5_3 :
  jacobiSym (2 * (5 : ℤ)) 3 = (ZMod.χ₈ 3 : ℤ) * jacobiSym (5 : ℤ) 3 :=
  jacobiSym_two_mul_of_odd _ _ (by decide)

/--
[jac4_N3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jac4_N3_5 : jacobiSym (4 * (-3 : ℤ)) 5 = -1 := by
norm_num

/--
[jacm_N3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacm_N3_5 : jacobiSym (-3 : ℤ) 5 = -1 := by
norm_num

/--
[jac2_N3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jac2_N3_5 : jacobiSym (2 * (-3 : ℤ)) 5 = 1 := by
norm_num

/--
[chi8_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma chi8_5 : (ZMod.χ₈ 5 : ℤ) = -1 := by
  have hat : jacobiSym (2 : ℤ) 5 = (ZMod.χ₈ 5 : ℤ) := jacobiSym.at_two (by decide)
  have hjac : jacobiSym (2 : ℤ) 5 = -1 := by norm_num
  rwa [← hat]

/--
[agreeRed4_N3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeRed4_N3_5 :
  jacobiSym (4 * (-3 : ℤ)) 5 = jacobiSym (-3 : ℤ) 5 := by
  rw [jac4_N3_5, jacm_N3_5]

/--
[agreeRed2_N3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeRed2_N3_5 :
  jacobiSym (2 * (-3 : ℤ)) 5 = (ZMod.χ₈ 5 : ℤ) * jacobiSym (-3 : ℤ) 5 := by
  rw [jac2_N3_5, chi8_5, jacm_N3_5]
  decide

/--
[bridgeRed4_N3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeRed4_N3_5 :
  jacobiSym (4 * (-3 : ℤ)) 5 = jacobiSym (-3 : ℤ) 5 :=
  jacobiSym_four_mul_of_odd _ _ (by decide)

/--
[bridgeRed2_N3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeRed2_N3_5 :
  jacobiSym (2 * (-3 : ℤ)) 5 = (ZMod.χ₈ 5 : ℤ) * jacobiSym (-3 : ℤ) 5 :=
  jacobiSym_two_mul_of_odd _ _ (by decide)

/--
[kronOddBase7_3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronOddBase7_3 : kroneckerSym (7 : ℤ) 3 = 1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (7 : ℤ) 3 = kroneckerAtPrime (7 : ℤ) 3 :=
    kroneckerSym_prime (7 : ℤ) 3 hp
  have hat : kroneckerAtPrime (7 : ℤ) 3 = legendreSym 3 (7 : ℤ) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (7 : ℤ) = jacobiSym (7 : ℤ) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (7 : ℤ)
  have hjac : jacobiSym (7 : ℤ) 3 = 1 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[kronOddBase7_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronOddBase7_5 : kroneckerSym (7 : ℤ) 5 = -1 := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : 5 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 5) := ⟨hp⟩
  have hprime : kroneckerSym (7 : ℤ) 5 = kroneckerAtPrime (7 : ℤ) 5 :=
    kroneckerSym_prime (7 : ℤ) 5 hp
  have hat : kroneckerAtPrime (7 : ℤ) 5 = legendreSym 5 (7 : ℤ) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 5 (7 : ℤ) = jacobiSym (7 : ℤ) 5 :=
    jacobiSym.legendreSym.to_jacobiSym 5 (7 : ℤ)
  have hjac : jacobiSym (7 : ℤ) 5 = -1 := by norm_num
  rw [hprime, hat, hleg, hjac]

/--
[kronOddComp7_15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma kronOddComp7_15 : kroneckerSym (7 : ℤ) 15 = -1 := by
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  have hmul : kroneckerSym (7 : ℤ) (3 * 5) =
    kroneckerSym (7 : ℤ) 3 * kroneckerSym (7 : ℤ) 5 :=
    kroneckerSym_mul (7 : ℤ) (by decide) 3 5
  rw [h15, hmul, kronOddBase7_3, kronOddBase7_5]
  decide

/--
[agreeMul7_3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeMul7_3_5 :
  kroneckerSym (7 : ℤ) 15 = kroneckerSym (7 : ℤ) 3 * kroneckerSym (7 : ℤ) 5 := by
  rw [kronOddComp7_15, kronOddBase7_3, kronOddBase7_5]
  decide

/--
[bridgeMul7_3_5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeMul7_3_5 :
  kroneckerSym (7 : ℤ) (3 * 5) =
    kroneckerSym (7 : ℤ) 3 * kroneckerSym (7 : ℤ) 5 :=
  kroneckerSym_mul_of_odd 7 3 5 (by decide) (by decide)

/--
[jacEqNeg1_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacEqNeg1_9 : jacobiSym (-1 : ℤ) 9 = 1 := by
norm_num

/--
[bridgeEqNeg1_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeEqNeg1_9 :
  kroneckerSym (-1 : ℤ) 9 = jacobiSym (-1 : ℤ) 9 :=
  kroneckerSym_eq_jacobiSym_of_odd (-1) 9 (by decide)

/--
[agreeOdd7_15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma agreeOdd7_15 :
  (ZMod.χ₄ 15 : ℤ) * jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs =
    kroneckerSym (7 : ℤ) 15 := by
  rw [chi15, jacComp7_15, kronOddComp7_15]
  decide

/--
[bridgeOdd7_15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeOdd7_15 :
  (ZMod.χ₄ 15 : ℤ) * jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs =
    kroneckerSym (7 : ℤ) 15 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four
    7 15 (by decide) (by decide)

/--
[jacOddNeg1_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacOddNeg1_9 : jacobiSym ((9 : ℕ) : ℤ) (-1 : ℤ).natAbs = 1 := by
norm_num

/--
[bridgeOddNeg1_9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma bridgeOddNeg1_9 :
  (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (-1 : ℤ).natAbs =
    kroneckerSym (-1 : ℤ) 9 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four
    (-1) 9 (by decide) (by decide)

/--
[scope_mod3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma scope_mod3 : (3 : ℤ) % 4 = 3 := by
decide

/--
[scope_modNeg5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma scope_modNeg5 : (-5 : ℤ) % 4 = 3 := by
decide

/--
[scope_mod7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma scope_mod7 : (7 : ℤ) % 4 = 3 := by
decide

/--
[scope_modNeg1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma scope_modNeg1 : (-1 : ℤ) % 4 = 3 := by
decide

/--
[scope_mod5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma scope_mod5 : (5 : ℤ) % 4 = 1 := by
decide

/--
[scope_odd7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma scope_odd7 : Odd (7 : ℕ) := by
decide

/--
[scope_odd9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma scope_odd9 : Odd (9 : ℕ) := by
decide

/--
[scope_odd15](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma scope_odd15 : Odd (15 : ℕ) := by
decide


-- created on 2026-10-23
