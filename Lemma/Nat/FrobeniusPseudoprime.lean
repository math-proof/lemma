import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.FrobeniusPseudoprime
open Polynomial
open Nat


namespace Polynomial

/--
[IsGreatestCommonMonicDivisor.unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
lemma IsGreatestCommonMonicDivisor.unfold
  [CommRing R]
  {h g₁ g₂ : _root_.Polynomial R} :
-- imply
  IsGreatestCommonMonicDivisor h g₁ g₂ ↔
    (h.Monic ∧ g₁.Monic ∧ g₂.Monic ∧
    Ideal.span ({g₁, g₂} : Set (_root_.Polynomial R)) =
    Ideal.span ({h} : Set (_root_.Polynomial R))) :=
-- proof
  Iff.rfl
end Polynomial


namespace Nat

/--
[IsFrobeniusProbablePrime.unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
lemma IsFrobeniusProbablePrime.unfold
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
    jacobiSym f.discr n) :=
-- proof
  Iff.rfl

end Nat

namespace Nat

/--
[IsFrobeniusProbablePrime.monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
lemma IsFrobeniusProbablePrime.monic
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusProbablePrime n f) :
-- imply
  f.Monic :=
-- proof
  h.1

end Nat

namespace Nat

/--
[IsFrobeniusProbablePrime.odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
lemma IsFrobeniusProbablePrime.odd
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusProbablePrime n f) :
-- imply
  Odd n :=
-- proof
  h.2.1

end Nat

namespace Nat

/--
[IsFrobeniusProbablePrime.one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
lemma IsFrobeniusProbablePrime.one_lt
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusProbablePrime n f) :
-- imply
  1 < n :=
-- proof
  h.2.2.1

end Nat

namespace Nat

/--
[IsFrobeniusPseudoprime.unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
lemma IsFrobeniusPseudoprime.unfold
  {n : ℕ}
  {f : _root_.Polynomial ℤ} :
-- imply
  IsFrobeniusPseudoprime n f ↔
    (¬ n.Prime ∧ IsFrobeniusProbablePrime n f) :=
-- proof
  Iff.rfl

end Nat

namespace Nat

/--
[IsFrobeniusPseudoprime.composite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
lemma IsFrobeniusPseudoprime.composite
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusPseudoprime n f) :
-- imply
  ¬ n.Prime :=
-- proof
  h.1

end Nat

namespace Nat

/--
[IsFrobeniusPseudoprime.probablePrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FrobeniusPseudoprime.lean)
-/
@[path]
lemma IsFrobeniusPseudoprime.probablePrime
  {n : ℕ}
  {f : _root_.Polynomial ℤ}
-- given
  (h : IsFrobeniusPseudoprime n f) :
-- imply
  IsFrobeniusProbablePrime n f :=
-- proof
  h.2

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
