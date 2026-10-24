/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Frobenius/Splitting.lean -/


import sympy.atlas.RingTheory.Frobenius.Splitting
import Lemma.Ideal.Frobenius.Splitting


open Ideal
open scoped Pointwise

example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    {p : Ideal A} {P : Ideal B} [P.IsPrime] [P.LiesOver p] :
    MulAction.stabilizer G P = ⊥ ↔ (primesOver p B).ncard = Nat.card G :=
  Ideal.stabilizer_eq_bot_iff_ncard_primesOver_eq_card

example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    {p : Ideal A} {P : Ideal B} [P.IsPrime] [P.LiesOver p]
    [Finite (B ⧸ P)]
    (hgen : ∀ g ∈ MulAction.stabilizer G P,
      ∃ n : ℕ, g = arithFrobAt A G P ^ n) :
    arithFrobAt A G P = 1 ↔ (Ideal.primesOver p B).ncard = Nat.card G :=
  arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates hgen

example {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    {p : Ideal A} [p.IsPrime] {P : Ideal B} [P.IsPrime] [P.LiesOver p]
    [PerfectField p.ResidueField]
    [Finite (B ⧸ P)] [Algebra.IsUnramifiedAt A P] (g : G)
    (hg : g ∈ MulAction.stabilizer G P) :
    ∃ n : ℕ, g = arithFrobAt A G P ^ n :=
  arithFrobAt_generates_stabilizer_of_isUnramifiedAt (p := p) g hg

example {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    {p : Ideal A} [p.IsPrime] {P : Ideal B} [P.IsPrime] [P.LiesOver p]
    [Finite (B ⧸ P)] [Algebra.IsUnramifiedAt A P] :
    arithFrobAt A G P = 1 ↔ (Ideal.primesOver p B).ncard = Nat.card G :=
  arithFrobAt_eq_one_iff_ncard_primesOver_eq_card
