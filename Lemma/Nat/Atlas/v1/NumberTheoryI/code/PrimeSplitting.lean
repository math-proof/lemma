import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.PrimeSplitting
open Ideal Module


/--
[liesOver_of_dvd_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma liesOver_of_dvd_map
  [CommRing A]
  [CommRing B]
  [IsDedekindDomain B]
  [Algebra A B]
  {p : Ideal A}
  {P : Ideal B}
  [hp : p.IsMaximal]
  [hP : P.IsPrime]
-- given
  (hdvd : P ∣ Ideal.map (algebraMap A B) p) :
-- imply
  P.LiesOver p := by
-- proof
  constructor
  have hle : Ideal.map (algebraMap A B) p ≤ P := Ideal.dvd_iff_le.mp hdvd
  have hle' : p ≤ P.under A := Ideal.map_le_iff_le_comap.mp hle
  have hne : P.under A ≠ ⊤ := Ideal.comap_ne_top (algebraMap A B) hP.ne_top
  exact hp.eq_of_le hne hle'

/--
[dvd_map_of_liesOver](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma dvd_map_of_liesOver
  [CommRing A]
  [CommRing B]
  [IsDedekindDomain B]
  [Algebra A B]
  {p : Ideal A}
  {P : Ideal B}
  [hlo : P.LiesOver p] :
-- imply
  P ∣ Ideal.map (algebraMap A B) p := by
-- proof
  rwa [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]

/--
[dvd_map_iff_liesOver](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma dvd_map_iff_liesOver
  [CommRing A]
  [CommRing B]
  [IsDedekindDomain B]
  [Algebra A B]
  {p : Ideal A}
  {P : Ideal B}
  [hp : p.IsMaximal]
  [hP : P.IsPrime] :
-- imply
  P ∣ Ideal.map (algebraMap A B) p ↔ P.LiesOver p :=
-- proof
  ⟨liesOver_of_dvd_map, fun h => by haveI := h; exact dvd_map_of_liesOver⟩
section RamificationInertiaDef
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] [Algebra A B]

/--
[ramificationIdx_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma ramificationIdx_def
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {p : Ideal A}
  {P : Ideal B} :
-- imply
  Ideal.ramificationIdx p P = sSup {n | Ideal.map (algebraMap A B) p ≤ P ^ n} :=
-- proof
  rfl

/--
[inertiaDeg_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma inertiaDeg_def
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {p : Ideal A}
  {P : Ideal B}
  [P.LiesOver p] :
-- imply
  Ideal.inertiaDeg p P = finrank (A ⧸ p) (B ⧸ P) :=
-- proof
  Ideal.inertiaDeg_algebraMap p P
end RamificationInertiaDef
section TowerRamification
variable {A : Type*} [CommRing A] [IsDomain A]
variable {B : Type*} [CommRing B] [IsDedekindDomain B]
variable {C : Type*} [CommRing C] [IsDedekindDomain C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/--
[ramificationIdx_mul_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma ramificationIdx_mul_tower
  [CommRing A]
  [IsDomain A]
  [CommRing B]
  [IsDedekindDomain B]
  [CommRing C]
  [IsDedekindDomain C]
  [Algebra A B]
  [Algebra B C]
  [Algebra A C]
  [IsScalarTower A B C]
  [Module.IsTorsionFree A B]
  [Module.IsTorsionFree B C]
  {p : Ideal A}
  {P : Ideal B}
  {Q : Ideal C}
  [Q.IsPrime]
  [Q.LiesOver P]
  [P.LiesOver p] :
-- imply
  Ideal.ramificationIdx p Q = Ideal.ramificationIdx p P * Ideal.ramificationIdx P Q :=
-- proof
  Ideal.ramificationIdx_algebra_tower' p P Q
end TowerRamification
section TowerInertia
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B]
variable {C : Type*} [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/--
[inertiaDeg_mul_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma inertiaDeg_mul_tower
  [CommRing A]
  [CommRing B]
  [CommRing C]
  [Algebra A B]
  [Algebra B C]
  [Algebra A C]
  [IsScalarTower A B C]
  {p : Ideal A}
  {P : Ideal B}
  {Q : Ideal C}
  [p.IsMaximal]
  [P.IsMaximal]
  [P.LiesOver p]
  [Q.LiesOver P] :
-- imply
  Ideal.inertiaDeg p Q = Ideal.inertiaDeg p P * Ideal.inertiaDeg P Q :=
-- proof
  Ideal.inertiaDeg_algebra_tower p P Q
end TowerInertia
section TowerMultiplicativity
variable {A : Type*} [CommRing A] [IsDomain A]
variable {B : Type*} [CommRing B] [IsDedekindDomain B]
variable {C : Type*} [CommRing C] [IsDedekindDomain C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/--
[ramificationIdx_inertiaDeg_mul_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma ramificationIdx_inertiaDeg_mul_tower
  [CommRing A]
  [IsDomain A]
  [CommRing B]
  [IsDedekindDomain B]
  [CommRing C]
  [IsDedekindDomain C]
  [Algebra A B]
  [Algebra B C]
  [Algebra A C]
  [IsScalarTower A B C]
  [Module.IsTorsionFree A B]
  [Module.IsTorsionFree B C]
  {p : Ideal A}
  {P : Ideal B}
  {Q : Ideal C}
  [p.IsMaximal]
  [P.IsMaximal]
  [Q.IsPrime]
  [Q.LiesOver P]
  [P.LiesOver p] :
-- imply
  Ideal.ramificationIdx p Q = Ideal.ramificationIdx p P * Ideal.ramificationIdx P Q ∧ Ideal.inertiaDeg p Q = Ideal.inertiaDeg p P * Ideal.inertiaDeg P Q :=
-- proof
  ⟨Ideal.ramificationIdx_algebra_tower' p P Q,
    Ideal.inertiaDeg_algebra_tower p P Q⟩

/--
[lemma_5_30](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma lemma_5_30
  [CommRing A]
  [IsDomain A]
  [CommRing B]
  [IsDedekindDomain B]
  [CommRing C]
  [IsDedekindDomain C]
  [Algebra A B]
  [Algebra B C]
  [Algebra A C]
  [IsScalarTower A B C]
  [Module.IsTorsionFree A B]
  [Module.IsTorsionFree B C]
  {p : Ideal A}
  {P : Ideal B}
  {Q : Ideal C}
  [p.IsMaximal]
  [P.IsMaximal]
  [Q.IsPrime]
  [Q.LiesOver P]
  [P.LiesOver p] :
-- imply
  Ideal.ramificationIdx p Q = Ideal.ramificationIdx p P * Ideal.ramificationIdx P Q ∧ Ideal.inertiaDeg p Q = Ideal.inertiaDeg p P * Ideal.inertiaDeg P Q :=
-- proof
  ramificationIdx_inertiaDeg_mul_tower p P Q
end TowerMultiplicativity
section IntegralClosureTower

/--
[isIntegralClosure_tower_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma isIntegralClosure_tower_top
  {A : Type*}
  [CommRing A]
  {B : Type*}
  [CommRing B]
  {C : Type*}
  [CommRing C]
  {M : Type*}
  [CommRing M]
  [Algebra A B]
  [Algebra A M]
  [Algebra B M]
  [Algebra C M]
  [IsScalarTower A B M]
  [IsIntegralClosure C A M]
  [Algebra.IsIntegral A B] :
-- imply
  IsIntegralClosure C B M :=
-- proof
  IsIntegralClosure.tower_top (R := A)

/--
[lemma_5_30_integral_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma lemma_5_30_integral_closure
  {A : Type*}
  [CommRing A]
  {B : Type*}
  [CommRing B]
  {C : Type*}
  [CommRing C]
  {M : Type*}
  [CommRing M]
  [Algebra A B]
  [Algebra A M]
  [Algebra B M]
  [Algebra C M]
  [IsScalarTower A B M]
  [IsIntegralClosure C A M]
  [Algebra.IsIntegral A B] :
-- imply
  IsIntegralClosure C B M :=
-- proof
  isIntegralClosure_tower_top A B C M
end IntegralClosureTower
section QuotientDimension
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {S : Type*} [CommRing S] [IsDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra K L] [Algebra R L]
variable [IsScalarTower R K L] [IsScalarTower R S L]
variable [Module.Finite R S]

/--
[dim_quotient_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma dim_quotient_eq_finrank
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDomain S]
  [Algebra R S]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra R K]
  [IsFractionRing R K]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R K L]
  [IsScalarTower R S L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal] :
-- imply
  finrank (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p) = finrank K L :=
-- proof
  Ideal.finrank_quotient_map p K L
end QuotientDimension
section FundamentalIdentity
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra K L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S]

/--
[sum_ef_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma sum_ef_eq_degree
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
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
  ∑ P ∈ primesOverFinset p S, Ideal.ramificationIdx p P * Ideal.inertiaDeg p P = finrank K L :=
-- proof
  Ideal.sum_ramification_inertia S K L hp0
end FundamentalIdentity
section RamificationBounds
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra K L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S]
variable [NoZeroSMulDivisors R S]

/--
[ramificationIdx_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma ramificationIdx_pos
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
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
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
  {P : Ideal S}
  [P.IsPrime]
  [P.LiesOver p]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  1 ≤ Ideal.ramificationIdx p P :=
-- proof
  Nat.pos_iff_ne_zero.mpr (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0)

/--
[ramificationIdx_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma ramificationIdx_le
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
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
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
  {P : Ideal S}
  [P.IsPrime]
  [P.LiesOver p] :
-- imply
  Ideal.ramificationIdx p P ≤ finrank K L :=
-- proof
  Ideal.ramificationIdx_le_finrank S K L P

/--
[inertiaDeg_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma inertiaDeg_pos
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
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
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
  {P : Ideal S}
  [P.IsPrime]
  [P.LiesOver p] :
-- imply
  1 ≤ Ideal.inertiaDeg p P :=
-- proof
  Ideal.inertiaDeg_pos p P

/--
[inertiaDeg_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma inertiaDeg_le
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
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
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
  {P : Ideal S}
  [P.IsPrime]
  [P.LiesOver p]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  Ideal.inertiaDeg p P ≤ finrank K L :=
-- proof
  Ideal.inertiaDeg_le_finrank S K L P hp0

/--
[card_primes_over_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma card_primes_over_pos
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
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
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  1 ≤ Finset.card (primesOverFinset p S) := by
-- proof
  rw [Finset.one_le_card]
  obtain ⟨⟨Q, hQ⟩⟩ : Nonempty (Ideal.primesOver p S) := Ideal.nonempty_primesOver p
  exact ⟨Q, (mem_primesOverFinset_iff hp0 _).mpr hQ⟩

/--
[card_primes_over_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean)
-/
@[path]
lemma card_primes_over_le
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
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
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  Finset.card (primesOverFinset p S) ≤ finrank K L :=
-- proof
  Ideal.card_primesOverFinset_le_finrank S K L hp0
end RamificationBounds
section SplittingTerminology
variable {A : Type*} [CommRing A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra A B]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra B L] [IsFractionRing B L]
variable [Algebra K L] [Algebra A L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Module.Finite A B]


-- created on 2026-10-23
