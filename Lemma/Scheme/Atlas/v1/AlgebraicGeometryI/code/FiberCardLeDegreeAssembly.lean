import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.FiberCardLeDegreeAssembly
open Module Ideal Polynomial FiberDegreeBound
open scoped Classical


/--
[lec6_lemma13_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberCardLeDegreeAssembly.lean)
-/
@[path]
lemma lec6_lemma13_chain
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {α : L} :
-- imply
  (minpoly K α).roots.toFinset.card ≤ finrank K L :=
-- proof
  (card_roots_le_deg (minpoly K α)).trans (minpoly_natDegree_le_finrank α)
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/--
[lec6_lemma13_fiber_card_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberCardLeDegreeAssembly.lean)
-/
@[path]
lemma lec6_lemma13_fiber_card_le_degree
  [CommRing B]
  [IsDomain B]
  [IsNoetherianRing B]
  [IsIntegrallyClosed B]
  [CommRing A]
  [IsDomain A]
  [Algebra B A]
  [Module.Finite B A]
  [NoZeroSMulDivisors B A]
  {𝔭 : Ideal B}
  [𝔭.IsPrime] :
-- imply
  Nat.card {q : Ideal A | q.IsPrime ∧ q.comap (algebraMap B A) = 𝔭} ≤ finrank (FractionRing B) (FractionRing A) :=
-- proof
  lec6_fiber_card_le_degree_general 𝔭

/--
[lec6_lemma13_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberCardLeDegreeAssembly.lean)
-/
@[path]
lemma lec6_lemma13_dedekind
  [CommRing R]
  [CommRing S]
  [IsDedekindDomain R]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
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
  fdb_fiber_card_le_degree K L hp0

/--
[lec6_degree_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberCardLeDegreeAssembly.lean)
-/
@[path]
lemma lec6_degree_eq_finrank
  {B A : Type*}
  [CommRing B]
  [IsDomain B]
  [CommRing A]
  [IsDomain A]
  [Algebra B A]
  [FaithfulSMul B A]
  [Module.Finite B A] :
-- imply
  degree B A = finrank B A :=
-- proof
  degree_eq_finrank B A


-- created on 2026-10-23
