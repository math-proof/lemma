import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.Frobenius.Splitting
open scoped Pointwise
open Ideal


namespace Ideal

/--
[stabilizer_eq_bot_iff_ncard_primesOver_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean)
-/
@[path]
lemma stabilizer_eq_bot_iff_ncard_primesOver_eq_card
  [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A}
  {P : Ideal B} [P.IsPrime] [P.LiesOver p] :
-- imply
  MulAction.stabilizer G P = ⊥ ↔ (primesOver p B).ncard = Nat.card G := by
-- proof
  have hfund : (primesOver p B).ncard * Nat.card (MulAction.stabilizer G P)
    = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A B G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hNpos : (primesOver p B).ncard ≠ 0 := by
    grind [Nat.card_pos]
  rw [← Subgroup.card_eq_one]
  constructor
  · intro hE1
    rwa [hE1, mul_one] at hfund
  · intro hNC
    have h1 : (primesOver p B).ncard * Nat.card (MulAction.stabilizer G P)
      = (primesOver p B).ncard * 1 := by
      rw [hfund, hNC, mul_one]
    exact mul_left_cancel₀ hNpos h1
end Ideal
section Conditional
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A} {P : Ideal B} [P.IsPrime] [P.LiesOver p]


/--
[arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean)
-/
@[path]
lemma arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates
  [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A}
  {P : Ideal B} [P.IsPrime] [P.LiesOver p] [Finite (B ⧸ P)]
-- given
  (hgen : ∀ g ∈ MulAction.stabilizer G P, ∃ n : ℕ, g = arithFrobAt A G P ^ n) :
-- imply
  arithFrobAt A G P = 1 ↔ (Ideal.primesOver p B).ncard = Nat.card G := by
-- proof
  have hmem : arithFrobAt A G P ∈ MulAction.stabilizer G P :=
    IsArithFrobAt.arithFrobAt_mem_stabilizer A G P
  have hstab : MulAction.stabilizer G P = ⊥ ↔ arithFrobAt A G P = 1 := by
    constructor
    · intro h
      rw [h] at hmem
      exact Subgroup.mem_bot.mp hmem
    · intro h
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨n, hn⟩ := hgen g hg
      rw [h, one_pow] at hn
      exact Subgroup.mem_bot.mpr hn
  rwa [← hstab]
end Conditional
section Unramified
variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [Module.Flat A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B]
  {p : Ideal A} [p.IsPrime] {P : Ideal B} [P.IsPrime] [P.LiesOver p]
  [PerfectField p.ResidueField]

/--
[arithFrobAt_generates_stabilizer_of_isUnramifiedAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean)
-/
@[path]
lemma arithFrobAt_generates_stabilizer_of_isUnramifiedAt
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Flat A B] [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B] [PerfectField p.ResidueField]
  {P : Ideal B} [P.IsPrime] [Finite (B ⧸ P)] [Algebra.IsUnramifiedAt A P]
  {p : Ideal A} [p.IsPrime] [P.LiesOver p] :
-- imply
  ∀ g ∈ MulAction.stabilizer G P,
    ∃ n : ℕ, g = arithFrobAt A G P ^ n := by
-- proof
  let _ : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  let _ : P.IsMaximal :=
    Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain (B ⧸ P))
  let _ : p.IsMaximal := Ideal.IsMaximal.of_isMaximal_liesOver P p
  let _ : Finite (A ⧸ p) :=
    Finite.of_injective (algebraMap (A ⧸ p) (B ⧸ P))
      (FaithfulSMul.algebraMap_injective (A ⧸ p) (B ⧸ P))
  let _ : Fintype (A ⧸ p) := Fintype.ofFinite (A ⧸ p)
  let _ : Fintype (B ⧸ P) := Fintype.ofFinite (B ⧸ P)
  let _ : Field (A ⧸ p) := Ideal.Quotient.field p
  let _ : Field (B ⧸ P) := Ideal.Quotient.field P
  have hram : P.ramificationIdx A = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hcard : Nat.card (P.inertia G) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P G, hram]
  have hbot : P.inertia G = ⊥ := Subgroup.card_eq_one.mp hcard
  have hrho : Function.Injective (Ideal.Quotient.stabilizerHom P p G) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hmap : (Ideal.Quotient.stabilizerHom P p G).ker.map
      (Subgroup.subtype _) = ⊥ := by
      rw [Ideal.Quotient.map_ker_stabilizer_subtype, hbot]
    exact
      (Subgroup.map_eq_bot_iff_of_injective
        (Ideal.Quotient.stabilizerHom P p G).ker
        (Subgroup.subtype_injective (MulAction.stabilizer G P))).mp hmap
  have hmem : arithFrobAt A G P ∈ MulAction.stabilizer G P :=
    IsArithFrobAt.arithFrobAt_mem_stabilizer A G P
  have hF : Ideal.Quotient.stabilizerHom P p G ⟨arithFrobAt A G P, hmem⟩
    = FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ p) (B ⧸ P) := by
    ext x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hFrob := (IsArithFrobAt.arithFrobAt A G P).mk_apply b
    simpa [Ideal.Quotient.stabilizerHom_apply,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← P.over_def p,
      Nat.card_eq_fintype_card] using hFrob
  intro g hg
  obtain ⟨⟨n, _⟩, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (A ⧸ p)
      (B ⧸ P)).2 (Ideal.Quotient.stabilizerHom P p G ⟨g, hg⟩)
  have hcon : (⟨g, hg⟩ : MulAction.stabilizer G P)
    = ⟨arithFrobAt A G P, hmem⟩ ^ n := by
    apply hrho
    rwa [map_pow, hF]
  have hpow : ((⟨arithFrobAt A G P, hmem⟩ ^ n :
    MulAction.stabilizer G P) : G) = arithFrobAt A G P ^ n :=
    Subgroup.coe_pow _ _ n
  have hval := congrArg (Subtype.val : MulAction.stabilizer G P → G) hcon
  rw [hpow] at hval
  exact ⟨n, hval⟩

/--
[arithFrobAt_eq_one_iff_ncard_primesOver_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean)
-/
@[path]
lemma arithFrobAt_eq_one_iff_ncard_primesOver_eq_card
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Flat A B] [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  {p : Ideal A} [p.IsPrime] [PerfectField p.ResidueField]
  {P : Ideal B} [P.IsPrime] [P.LiesOver p] [Finite (B ⧸ P)] [Algebra.IsUnramifiedAt A P] :
-- imply
  arithFrobAt A G P = 1 ↔ (Ideal.primesOver p B).ncard = Nat.card G :=
-- proof
  arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates
    (arithFrobAt_generates_stabilizer_of_isUnramifiedAt (p := p))
end Unramified


-- created on 2026-10-20
-- updated on 2026-10-26
