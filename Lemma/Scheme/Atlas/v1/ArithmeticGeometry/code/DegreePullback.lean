import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.DegreePullback
open Ideal Module Finset


/--
[degree_pullback_eq_mul_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DegreePullback.lean)
-/
@[path]
lemma degree_pullback_eq_mul_degree
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [IsDedekindDomain R]
  [Algebra k R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [Algebra k S]
  [IsScalarTower k R S]
  [Module.IsTorsionFree R S]
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
  pullbackDivisorDegree k R S p = Module.finrank K L * closedPointDegree k R p := by
-- proof
  unfold pullbackDivisorDegree closedPointDegree
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  have step1 : ∀ P ∈ primesOverFinset p S,
    p.ramificationIdx P * finrank k (S ⧸ P) =
    p.ramificationIdx P * p.inertiaDeg P * finrank k (R ⧸ p) := by
    intro P hP
    have hPprime : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
    have hPliesOver : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
    have htower : finrank k (S ⧸ P) = finrank (R ⧸ p) (S ⧸ P) * finrank k (R ⧸ p) :=
      (finrank_mul_finrank k (R ⧸ p) (S ⧸ P)).symm ▸ (mul_comm _ _)
    rw [htower, Ideal.inertiaDeg_algebraMap, mul_assoc]
  rw [Finset.sum_congr rfl step1]
  rw [← Finset.sum_mul]
  rw [Ideal.sum_ramification_inertia S K L hp0]


-- created on 2026-10-23
