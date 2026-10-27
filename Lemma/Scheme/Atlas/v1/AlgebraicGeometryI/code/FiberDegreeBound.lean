import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.FiberDegreeBound
open Module Ideal FiberDegreeBound


namespace FiberDegreeBound

/--
[degree_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma degree_eq_finrank
  {B A : Type*}
  [CommRing B]
  [IsDomain B]
  [CommRing A]
  [IsDomain A]
  [Module.Finite B A] :
-- imply
  degree B A = finrank B A := by
-- proof
  have : Algebra.IsAlgebraic B A := by
    constructor; intro x; exact (IsIntegral.of_finite B x).isAlgebraic
  exact Algebra.IsAlgebraic.finrank_of_isFractionRing B (FractionRing B) A (FractionRing A)
section FiberBoundGeneral
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
/-- General version of Lec 6, Lem 13: over a normal Noetherian base `B`, the
fiber of a finite morphism `Spec A → Spec B` has cardinality bounded by the
generic degree `[K(A) : K(B)]`. -/
end FiberBoundGeneral
section FiberBound
variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [NoZeroSMulDivisors R S]

end FiberDegreeBound

namespace FiberDegreeBound

/--
[fdb_fiber_card_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma fdb_fiber_card_le_degree
  [CommRing R]
  [CommRing S]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra R K]
  [IsFractionRing R K]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  (primesOverFinset p S).card ≤ finrank K L :=
-- proof
  Ideal.card_primesOverFinset_le_finrank S K L hp0

end FiberDegreeBound

namespace FiberDegreeBound

/--
[fdb_fundamental_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma fdb_fundamental_identity
  [CommRing R]
  [CommRing S]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra R K]
  [IsFractionRing R K]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  ∑ P ∈ primesOverFinset p S, p.ramificationIdx P * p.inertiaDeg P = finrank K L :=
-- proof
  Ideal.sum_ramification_inertia S K L hp0
section UnramifiedGeneral
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

end FiberDegreeBound

namespace FiberDegreeBound

/--
[fdb_isRamifiedAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma fdb_isRamifiedAt_iff
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  FdbIsRamifiedAt (S := S) K L p ↔ (primesOverFinset p S).card < finrank K L := by
-- proof
  unfold FdbIsRamifiedAt FdbIsUnramifiedAt
  constructor
  · intro h
    exact lt_of_le_of_ne (Ideal.card_primesOverFinset_le_finrank S K L hp0) h
  · intro h
    exact Nat.ne_of_lt h

end FiberDegreeBound

namespace FiberDegreeBound

/--
[fdb_unramified_implies_all_ef_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma fdb_unramified_implies_all_ef_one
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥)
  (hunr : FdbIsUnramifiedAt (S := S) K L p) :
-- imply
  ∀ P ∈ primesOverFinset p S, p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1 := by
-- proof
  unfold FdbIsUnramifiedAt at hunr
  have hfund := sum_ramification_inertia S K L hp0
  rw [← hunr] at hfund
  have hge1 : ∀ P ∈ primesOverFinset p S,
    1 ≤ p.ramificationIdx P * p.inertiaDeg P := by
    intro P hP
    have hPprime : P.IsPrime := ((mem_primesOverFinset_iff hp0 _).mp hP).1
    have hPover : P.LiesOver p := ((mem_primesOverFinset_iff hp0 _).mp hP).2
    have he : 0 < p.ramificationIdx P :=
      Nat.pos_of_ne_zero (IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0)
    have hf : 0 < p.inertiaDeg P := inertiaDeg_pos p P
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hall : ∀ P ∈ primesOverFinset p S,
    p.ramificationIdx P * p.inertiaDeg P = 1 := by
    intro P hP
    by_contra h
    have hlt : 1 < p.ramificationIdx P * p.inertiaDeg P :=
      Nat.lt_of_le_of_ne (hge1 P hP) (Ne.symm h)
    have : ∑ Q ∈ primesOverFinset p S, (1 : ℕ) <
      ∑ Q ∈ primesOverFinset p S,
        (p.ramificationIdx Q * p.inertiaDeg Q) :=
      Finset.sum_lt_sum hge1 ⟨P, hP, hlt⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  intro P hP
  have h1 := hall P hP
  exact ⟨Nat.eq_one_of_mul_eq_one_right h1, Nat.eq_one_of_mul_eq_one_left h1⟩

end FiberDegreeBound

namespace FiberDegreeBound

/--
[fdb_all_ef_one_implies_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma fdb_all_ef_one_implies_unramified
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥)
  (hef : ∀ P ∈ primesOverFinset p S, p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1) :
-- imply
  FdbIsUnramifiedAt (S := S) K L p := by
-- proof
  unfold FdbIsUnramifiedAt
  have hfund := sum_ramification_inertia S K L hp0
  have hone : ∑ P ∈ primesOverFinset p S,
    p.ramificationIdx P * p.inertiaDeg P =
    ∑ P ∈ primesOverFinset p S, 1 := by
    apply Finset.sum_congr rfl
    intro P hP
    obtain ⟨he, hf⟩ := hef P hP
    simp [he, hf]
  rwa [hone, Finset.sum_const, smul_eq_mul, mul_one] at hfund

end FiberDegreeBound

namespace FiberDegreeBound

/--
[fdb_isUnramifiedAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma fdb_isUnramifiedAt_iff
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  FdbIsUnramifiedAt (S := S) K L p ↔ ∀ P ∈ primesOverFinset p S, p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1 :=
-- proof
  ⟨fdb_unramified_implies_all_ef_one K L hp0, fdb_all_ef_one_implies_unramified K L hp0⟩

end FiberDegreeBound

namespace FiberDegreeBound

/--
[fdb_inertiaDeg_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma fdb_inertiaDeg_le_degree
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
  {P : Ideal S}
  [P.IsPrime]
  [P.LiesOver p]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  inertiaDeg p P ≤ finrank K L :=
-- proof
  Ideal.inertiaDeg_le_finrank S K L P hp0

end FiberDegreeBound

namespace FiberDegreeBound

/--
[fdb_ramificationIdx_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean)
-/
@[path]
lemma fdb_ramificationIdx_le_degree
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
  {P : Ideal S}
  [P.IsPrime]
  [P.LiesOver p] :
-- imply
  p.ramificationIdx P ≤ finrank K L :=
-- proof
  Ideal.ramificationIdx_le_finrank S K L P

end FiberDegreeBound


-- created on 2026-10-23
