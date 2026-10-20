import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Frobenius.Splitting
open scoped Pointwise
open Ideal


/--
[stabilizer_eq_bot_iff_ncard_primesOver_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean)
-/
@[path]
private lemma stabilizer_eq_bot_iff_ncard_primesOver_eq_card_eq
  [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A}
  {P : Ideal B} [P.IsPrime] [P.LiesOver p] :
-- imply
  MulAction.stabilizer G P = ⊥ ↔ (primesOver p B).ncard = Nat.card G := by
-- proof
  apply Ideal.stabilizer_eq_bot_iff_ncard_primesOver_eq_card

/--
[arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean)
-/
@[path]
private lemma arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates_eq
  [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A}
  {P : Ideal B} [P.IsPrime] [P.LiesOver p] [Finite (B ⧸ P)]
-- given
  (hgen : ∀ g ∈ MulAction.stabilizer G P, ∃ n : ℕ, g = arithFrobAt A G P ^ n) :
-- imply
  arithFrobAt A G P = 1 ↔ (Ideal.primesOver p B).ncard = Nat.card G := by
-- proof
  apply arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates hgen

/--
[arithFrobAt_generates_stabilizer_of_isUnramifiedAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean)
-/
@[path]
private lemma arithFrobAt_generates_stabilizer_of_isUnramifiedAt_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Flat A B] [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B] [PerfectField p.ResidueField]
  {P : Ideal B} [P.IsPrime] [Finite (B ⧸ P)] [Algebra.IsUnramifiedAt A P]
  {p : Ideal A} [p.IsPrime] [P.LiesOver p] :
-- imply
  ∀ g ∈ MulAction.stabilizer G P,
    ∃ n : ℕ, g = arithFrobAt A G P ^ n := by
-- proof
  apply arithFrobAt_generates_stabilizer_of_isUnramifiedAt p

/--
[arithFrobAt_eq_one_iff_ncard_primesOver_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean)
-/
@[path]
private lemma arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Flat A B] [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  {p : Ideal A} [p.IsPrime] [PerfectField p.ResidueField]
  {P : Ideal B} [P.IsPrime] [P.LiesOver p] [Finite (B ⧸ P)] [Algebra.IsUnramifiedAt A P] :
-- imply
  arithFrobAt A G P = 1 ↔ (Ideal.primesOver p B).ncard = Nat.card G := by
-- proof
  apply arithFrobAt_eq_one_iff_ncard_primesOver_eq_card


-- created on 2026-10-20
