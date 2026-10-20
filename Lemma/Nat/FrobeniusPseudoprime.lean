import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.FrobeniusPseudoprime
open Polynomial
open Nat


/--
[IsGreatestCommonMonicDivisor.unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
private lemma IsGreatestCommonMonicDivisor_unfold_eq
  [CommRing R]
  {h g₁ g₂ : _root_.Polynomial R} :
-- imply
  IsGreatestCommonMonicDivisor h g₁ g₂ ↔
    (h.Monic ∧ g₁.Monic ∧ g₂.Monic ∧
    Ideal.span ({g₁, g₂} : Set (_root_.Polynomial R)) =
    Ideal.span ({h} : Set (_root_.Polynomial R))) := by
-- proof
  apply Polynomial.IsGreatestCommonMonicDivisor.unfold h g₁ g₂

/--
[IsFrobeniusProbablePrime.unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
private lemma IsFrobeniusProbablePrime_unfold_eq
  {n : ℕ}
  {f : _root_.Polynomial ℤ} :
-- imply
  IsFrobeniusProbablePrime n f ↔
    (f.Monic ∧ Odd n ∧ 1 < n ∧
    _root_.Nat.Coprime n (Int.natAbs (f.eval 0 * f.discr)) ∧
    ∃ F fs : ℕ → _root_.Polynomial (ZMod n),
    ∃ q : ℕ → ℕ,
    fs 0 = f.map (Int.castRingHom (ZMod n)) ∧
    fs f.natDegree = 1 ∧
    (∀ i ∈ Finset.Icc 1 f.natDegree,
    IsGreatestCommonMonicDivisor (F i)
    (Polynomial.X ^ (n ^ i) - Polynomial.X : _root_.Polynomial (ZMod n))
    (fs (i - 1)) ∧ fs (i - 1) = F i * fs i) ∧
    (∀ i ∈ Finset.Icc 2 f.natDegree,
    F i ∣ (F i).comp (Polynomial.X ^ n : _root_.Polynomial (ZMod n))) ∧
    (∀ i ∈ Finset.Icc 1 f.natDegree, Even i → (F i).natDegree = i * q i) ∧
    (-1 : ℤ) ^
    Finset.sum (Finset.Icc 1 f.natDegree)
    (fun i => if i % 2 = 0 then q i else 0) =
    jacobiSym f.discr n) := by
-- proof
  apply Nat.IsFrobeniusProbablePrime.unfold n f

/--
[IsFrobeniusProbablePrime.monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
private lemma IsFrobeniusProbablePrime_monic_eq
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusProbablePrime n f) :
-- imply
  f.Monic := by
-- proof
  apply Nat.IsFrobeniusProbablePrime.monic h

/--
[IsFrobeniusProbablePrime.odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
private lemma IsFrobeniusProbablePrime_odd_eq
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusProbablePrime n f) :
-- imply
  Odd n := by
-- proof
  apply Nat.IsFrobeniusProbablePrime.odd h

/--
[IsFrobeniusProbablePrime.one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
private lemma IsFrobeniusProbablePrime_one_lt_eq
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusProbablePrime n f) :
-- imply
  1 < n := by
-- proof
  apply Nat.IsFrobeniusProbablePrime.one_lt h

/--
[IsFrobeniusPseudoprime.unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
private lemma IsFrobeniusPseudoprime_unfold_eq
  {n : ℕ}
  {f : _root_.Polynomial ℤ} :
-- imply
  IsFrobeniusPseudoprime n f ↔
    (¬ n.Prime ∧ IsFrobeniusProbablePrime n f) := by
-- proof
  apply Nat.IsFrobeniusPseudoprime.unfold n f

/--
[IsFrobeniusPseudoprime.composite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
private lemma IsFrobeniusPseudoprime_composite_eq
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusPseudoprime n f) :
-- imply
  ¬ n.Prime := by
-- proof
  apply Nat.IsFrobeniusPseudoprime.composite h

/--
[IsFrobeniusPseudoprime.probablePrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
private lemma IsFrobeniusPseudoprime_probablePrime_eq
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusPseudoprime n f) :
-- imply
  IsFrobeniusProbablePrime n f := by
-- proof
  apply Nat.IsFrobeniusPseudoprime.probablePrime h


-- created on 2026-10-20
