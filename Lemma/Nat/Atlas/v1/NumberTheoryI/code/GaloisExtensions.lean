import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.GaloisExtensions
open Ideal
open scoped Pointwise


/--
[left_gmodule_smul_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma left_gmodule_smul_add
  {G M : Type*}
  [Group G]
  [AddCommGroup M]
  [DistribMulAction G M]
  {σ : G}
  {a b : M} :
-- imply
  σ • (a + b) = σ • a + σ • b :=
-- proof
  smul_add σ a b
section GaloisActionOnIdeals
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[galois_action_fractional_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_action_fractional_ideal
  [CommRing B]
  {σ : G}
  {I : Ideal B}
  {x : B} :
-- imply
  x ∈ σ • I ↔ σ⁻¹ • x ∈ I :=
-- proof
  Ideal.mem_pointwise_smul_iff_inv_smul_mem

/--
[galois_action_mul_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_action_mul_compat
  [CommRing B]
  {σ : G}
  {I J : Ideal B} :
-- imply
  σ • (I * J) = σ • I * σ • J :=
-- proof
  MulSemiringAction.smul_mul σ I J

/--
[galois_action_preserves_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_action_preserves_prime
  [CommRing B]
  {σ : G}
  {I : Ideal B}
  [I.IsPrime] :
-- imply
  (σ • I).IsPrime :=
-- proof
  IsPrime.smul σ

/--
[galois_smul_ideal_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_smul_ideal_mem_iff
  [CommRing B]
  {σ : G}
  {I : Ideal B}
  {x : B} :
-- imply
  x ∈ σ • I ↔ σ⁻¹ • x ∈ I :=
-- proof
  Ideal.mem_pointwise_smul_iff_inv_smul_mem

/--
[theorem_7_2_sigma_preserves_fractional_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma theorem_7_2_sigma_preserves_fractional_ideal
  [CommRing B]
  {σ : G}
  {I : Ideal B}
  {x : B} :
-- imply
  x ∈ σ • I ↔ σ⁻¹ • x ∈ I :=
-- proof
  galois_smul_ideal_mem_iff G σ I x

/--
[galois_smul_ideal_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_smul_ideal_mul
  [CommRing B]
  {σ : G}
  {I J : Ideal B} :
-- imply
  σ • (I * J) = σ • I * σ • J :=
-- proof
  MulSemiringAction.smul_mul σ I J

/--
[theorem_7_2_gmodule_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma theorem_7_2_gmodule_structure
  [CommRing B]
  {σ : G}
  {I J : Ideal B} :
-- imply
  σ • (I * J) = σ • I * σ • J :=
-- proof
  galois_smul_ideal_mul G σ I J

/--
[galois_smul_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_smul_isPrime
  [CommRing B]
  {σ : G}
  {I : Ideal B}
  [I.IsPrime] :
-- imply
  (σ • I).IsPrime :=
-- proof
  IsPrime.smul σ

/--
[theorem_7_2_gset_on_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma theorem_7_2_gset_on_primes
  [CommRing B]
  {σ : G}
  {I : Ideal B}
  [I.IsPrime] :
-- imply
  (σ • I).IsPrime :=
-- proof
  galois_smul_isPrime G σ I

/--
[galois_smul_ideal_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_smul_ideal_add
  [CommRing B]
  {σ : G}
  {I J : Ideal B} :
-- imply
  σ • (I + J) = σ • I + σ • J :=
-- proof
  DistribMulAction.smul_add σ I J

/--
[theorem_7_2_gmodule_add_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma theorem_7_2_gmodule_add_compat
  [CommRing B]
  {σ : G}
  {I J : Ideal B} :
-- imply
  σ • (I + J) = σ • I + σ • J :=
-- proof
  galois_smul_ideal_add G σ I J
end GaloisActionOnIdeals
section GaloisActionTransitivity
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A}
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/--
[galois_action_on_ideals_isPretransitive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_action_on_ideals_isPretransitive
  [CommRing A]
  [CommRing B]
  [Algebra A B] :
-- imply
  MulAction.IsPretransitive G (primesOver p B) :=
-- proof
  isPretransitive_of_isGaloisGroup p G
end GaloisActionTransitivity
section TransitiveActionOnPrimes
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (p : Ideal A)
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/--
[galois_transitive_on_primes_above](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma galois_transitive_on_primes_above
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {P Q : Ideal B}
  [P.IsPrime]
  [P.LiesOver p]
  [Q.IsPrime]
  [Q.LiesOver p] :
-- imply
  ∃ σ : G, σ • P = Q :=
-- proof
  exists_smul_eq_of_isGaloisGroup p P Q G
end TransitiveActionOnPrimes
section ConstantRamificationInertia
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (p : Ideal A)
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/--
[ramificationIdx_constant_of_isGaloisGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma ramificationIdx_constant_of_isGaloisGroup
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {P Q : Ideal B}
  [P.IsPrime]
  [P.LiesOver p]
  [Q.IsPrime]
  [Q.LiesOver p] :
-- imply
  p.ramificationIdx P = p.ramificationIdx Q :=
-- proof
  ramificationIdx_eq_of_isGaloisGroup p P Q G

/--
[inertiaDeg_constant_of_isGaloisGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma inertiaDeg_constant_of_isGaloisGroup
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {P Q : Ideal B}
  [P.IsPrime]
  [P.LiesOver p]
  [Q.IsPrime]
  [Q.LiesOver p] :
-- imply
  p.inertiaDeg P = p.inertiaDeg Q :=
-- proof
  inertiaDeg_eq_of_isGaloisGroup p P Q G
end ConstantRamificationInertia
section EFGFormula
variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {p : Ideal A} [p.IsMaximal]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/--
[efg_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma efg_eq_degree
  [CommRing A]
  [IsDedekindDomain A]
-- given
  (hp : p ≠ ⊥) :
-- imply
  (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G :=
-- proof
  ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G
end EFGFormula
section DecompositionGroupDef
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[mem_decompositionGroup_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma mem_decompositionGroup_iff
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {Q : Ideal B}
  {σ : G} :
-- imply
  σ ∈ decompositionGroup G Q ↔ σ • Q = Q :=
-- proof
  MulAction.mem_stabilizer_iff
end DecompositionGroupDef
section DecompositionGroupProperties
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A}
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/--
[decompositionGroup_conjugate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma decompositionGroup_conjugate
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {P : Ideal B}
  {σ : G} :
-- imply
  decompositionGroup G (σ • P) = (decompositionGroup G P).map (MulAut.conj σ).toMonoidHom :=
-- proof
  MulAction.stabilizer_smul_eq_stabilizer_map_conj σ P

/--
[card_decompositionGroup_eq_ef](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma card_decompositionGroup_eq_ef
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [IsDedekindDomain A]
  [IsDedekindDomain B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {P : Ideal B}
  [P.LiesOver p]
  [P.IsMaximal]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
-- given
  (hp : p ≠ ⊥) :
-- imply
  Nat.card (decompositionGroup G P) = ramificationIdxIn p B * inertiaDegIn p B :=
-- proof
  Ideal.card_stabilizer_eq p hp P

/--
[index_decompositionGroup_eq_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma index_decompositionGroup_eq_g
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [IsDedekindDomain A]
  [IsDedekindDomain B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [p.IsMaximal]
  {P : Ideal B}
  [P.LiesOver p]
  [P.IsMaximal]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
-- given
  (hp : p ≠ ⊥) :
-- imply
  (decompositionGroup G P).index = (primesOver p B).ncard := by
-- proof
  have hef : Nat.card (MulAction.stabilizer G P) = ramificationIdxIn p B * inertiaDegIn p B :=
    Ideal.card_stabilizer_eq p hp P
  have hefg : (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G :=
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G
  have hcard : Nat.card (MulAction.stabilizer G P) * (MulAction.stabilizer G P).index = Nat.card G :=
    Subgroup.card_mul_index _
  rw [hef] at hcard
  have hef_pos : 0 < ramificationIdxIn p B * inertiaDegIn p B := by
    rw [← hef]; exact Nat.card_pos (α := ↥(MulAction.stabilizer G P))
  exact Nat.eq_of_mul_eq_mul_right hef_pos (by linarith)
end DecompositionGroupProperties
section ResidueFieldSurjection
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A}
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]

/--
[residueField_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma residueField_normal
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {Q : Ideal B}
  [Q.LiesOver p]
  [p.IsMaximal]
  [Q.IsMaximal] :
-- imply
  Normal (A ⧸ p) (B ⧸ Q) :=
-- proof
  Ideal.Quotient.normal G p Q
end ResidueFieldSurjection
section InertiaGroupDef
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[inertiaGroup_le_decompositionGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma inertiaGroup_le_decompositionGroup
  [CommRing B]
  {Q : Ideal B} :
-- imply
  inertiaGroup G Q ≤ decompositionGroup G Q :=
-- proof
  Ideal.inertia_le_stabilizer Q
end InertiaGroupDef
section InertiaDecompositionExactSequence
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A}
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
attribute [local instance] Ideal.Quotient.field

/--
[card_inertiaGroup_eq_e_mul_insepDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma card_inertiaGroup_eq_e_mul_insepDegree
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [IsDedekindDomain A]
  [IsDedekindDomain B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [p.IsMaximal]
  {P : Ideal B}
  [P.LiesOver p]
  [P.IsMaximal]
-- given
  (hp : p ≠ ⊥) :
-- imply
  Nat.card (inertiaGroup G P) = ramificationIdxIn p B * Field.finInsepDegree (A ⧸ p) (B ⧸ P) := by
-- proof
  have h_exact := Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P
  have h_index : ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).index =
    Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
    Nat.card_congr h_exact.toEquiv
  have h_lagrange := ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index
  rw [h_index, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv] at h_lagrange
  haveI : Normal (A ⧸ p) (B ⧸ P) := Ideal.Quotient.normal G p P
  have h_aut_sep : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) =
    Field.finSepDegree (A ⧸ p) (B ⧸ P) :=
    Nat.card_congr (Normal.algHomEquivAut (A ⧸ p) (AlgebraicClosure (B ⧸ P)) (B ⧸ P)).symm
  rw [h_aut_sep] at h_lagrange
  have h_gef := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G
  have h_orbit := Algebra.IsInvariant.orbit_eq_primesOver A B G p P
  have h_gD : (primesOver p B).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
    rw [← h_orbit]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hg_pos : 0 < (primesOver p B).ncard := by
    by_contra hg; simp only [not_lt, Nat.le_zero] at hg
    rw [hg, zero_mul] at h_gef; linarith [Nat.card_pos (α := G)]
  have h_D_eq : Nat.card (MulAction.stabilizer G P) =
    ramificationIdxIn p B * inertiaDegIn p B :=
    Nat.eq_of_mul_eq_mul_left hg_pos (h_gD.trans h_gef.symm)
  rw [h_D_eq, inertiaDegIn_eq_inertiaDeg p P G, inertiaDeg_algebraMap,
    ← Field.finSepDegree_mul_finInsepDegree (A ⧸ p) (B ⧸ P)] at h_lagrange
  have h_rw : ramificationIdxIn p B * (Field.finSepDegree (A ⧸ p) (B ⧸ P) *
    Field.finInsepDegree (A ⧸ p) (B ⧸ P)) =
    (ramificationIdxIn p B * Field.finInsepDegree (A ⧸ p) (B ⧸ P)) *
      Field.finSepDegree (A ⧸ p) (B ⧸ P) := by ring
  rw [h_rw] at h_lagrange
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne _)) h_lagrange

/--
[card_inertiaGroup_eq_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma card_inertiaGroup_eq_e
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [IsDedekindDomain A]
  [IsDedekindDomain B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {P : Ideal B}
  [P.LiesOver p]
  [P.IsMaximal]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
-- given
  (hp : p ≠ ⊥) :
-- imply
  Nat.card (inertiaGroup G P) = ramificationIdxIn p B :=
-- proof
  Ideal.card_inertia_eq_ramificationIdxIn p hp P
end InertiaDecompositionExactSequence
section FieldTower
variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}
  (P : Ideal B) [P.LiesOver p]
  [FiniteDimensional K L] [MulSemiringAction (L ≃ₐ[K] L) B]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Ring.HasFiniteQuotients A] [P.IsMaximal]

/--
[finrank_over_inertiaField_eq_ramificationIdx](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma finrank_over_inertiaField_eq_ramificationIdx
  {A K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  {E : Type*}
  [Field E]
  [Algebra E L]
  [IsInertiaField K L P E]
-- given
  (hp : p ≠ ⊥) :
-- imply
  Module.finrank E L = ramificationIdxIn p B :=
-- proof
  IsInertiaField.rank_left A K L P E hp

/--
[finrank_inertiaField_over_decompositionField_eq_inertiaDeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma finrank_inertiaField_over_decompositionField_eq_inertiaDeg
  {A K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  {D : Type*}
  [Field D]
  [Algebra D L]
  [IsDecompositionField K L P D]
  {E : Type*}
  [Field E]
  [Algebra E L]
  [IsInertiaField K L P E]
  [IsGalois K L]
  [Algebra K D]
  [Algebra K E]
  [Algebra D E]
  [IsScalarTower K D E]
  [IsScalarTower K E L]
  [IsScalarTower K D L]
-- given
  (hp : p ≠ ⊥) :
-- imply
  Module.finrank D E = inertiaDegIn p B :=
-- proof
  IsInertiaField.rank_decompositionField A K L P D E hp

/--
[finrank_decompositionField_eq_ncard_primesOver](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma finrank_decompositionField_eq_ncard_primesOver
  {A K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  {D : Type*}
  [Field D]
  [Algebra D L]
  [IsDecompositionField K L P D]
  [IsGalois K L]
  [Algebra K D]
  [IsScalarTower K D L]
-- given
  (hp : p ≠ ⊥) :
-- imply
  Module.finrank K D = (primesOver p B).ncard :=
-- proof
  IsDecompositionField.rank_right A K L P D hp

/--
[finrank_over_decompositionField_eq_ef](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma finrank_over_decompositionField_eq_ef
  {A K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  {D : Type*}
  [Field D]
  [Algebra D L]
  [IsDecompositionField K L P D]
-- given
  (hp : p ≠ ⊥) :
-- imply
  Module.finrank D L = ramificationIdxIn p B * inertiaDegIn p B :=
-- proof
  IsDecompositionField.rank_left A K L P D hp
end FieldTower
section IntermediateExtensionGroups
variable {B : Type*} [Ring B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[stabilizer_subgroupOf_and_inertia_subgroupOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma stabilizer_subgroupOf_and_inertia_subgroupOf
  [Ring B]
  {Q : Ideal B}
  {H : Subgroup G} :
-- imply
  (MulAction.stabilizer G Q).subgroupOf H = MulAction.stabilizer H Q ∧ (Q.inertia G).subgroupOf H = Q.inertia H :=
-- proof
  ⟨by ext ⟨h, hH⟩; simp [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf],
    AddSubgroup.subgroupOf_inertia Q.toAddSubgroup H⟩

/--
[decompositionGroup_subgroupOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma decompositionGroup_subgroupOf
  [Ring B]
  {Q : Ideal B}
  {H : Subgroup G} :
-- imply
  (MulAction.stabilizer G Q).subgroupOf H = MulAction.stabilizer H Q :=
-- proof
  (stabilizer_subgroupOf_and_inertia_subgroupOf G Q H).1

/--
[inertiaGroup_subgroupOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma inertiaGroup_subgroupOf
  [Ring B]
  {Q : Ideal B}
  {H : Subgroup G} :
-- imply
  (Q.inertia G).subgroupOf H = Q.inertia H :=
-- proof
  (stabilizer_subgroupOf_and_inertia_subgroupOf G Q H).2
end IntermediateExtensionGroups
section UnramifiedSplitCharacterization
variable (K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing B] [Algebra B L] [MulSemiringAction (L ≃ₐ[K] L) B]

/--
[inertiaField_is_fixedField_of_inertiaGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma inertiaField_is_fixedField_of_inertiaGroup
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  {P : Ideal B}
  [IsGalois K L] :
-- imply
  IsInertiaField K L P (FixedPoints.intermediateField (P.inertia (L ≃ₐ[K] L)) : IntermediateField K L) :=
-- proof
  inferInstance

/--
[decompositionField_is_fixedField_of_decompositionGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma decompositionField_is_fixedField_of_decompositionGroup
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  {P : Ideal B}
  [IsGalois K L] :
-- imply
  IsDecompositionField K L P (FixedPoints.intermediateField (MulAction.stabilizer (L ≃ₐ[K] L) P) : IntermediateField K L) :=
-- proof
  inferInstance

/--
[Subgroup.le_of_card_subgroupOf_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma Subgroup.le_of_card_subgroupOf_eq'
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Group G]
  {H K : Subgroup G}
  [Finite H]
-- given
  (h : Nat.card (H.subgroupOf K) = Nat.card H) :
-- imply
  H ≤ K := by
-- proof
  intro x hx
  let f : (H.subgroupOf K) → H := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, Subgroup.mem_subgroupOf.mp hg⟩
  have hf_inj : Function.Injective f := by
    intro ⟨⟨g₁, _⟩, _⟩ ⟨⟨g₂, _⟩, _⟩ heq
    simp only [f, Subtype.mk.injEq] at heq
    exact Subtype.ext (Subtype.ext heq)
  have hf_bij := hf_inj.bijective_of_nat_card_le (h ▸ le_refl _)
  obtain ⟨⟨⟨g, hg_K⟩, hg_H⟩, hg_eq⟩ := hf_bij.2 ⟨x, hx⟩
  simp only [f, Subtype.mk.injEq] at hg_eq
  rw [← hg_eq]; exact hg_K

/--
[card_inertia_tower_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma card_inertia_tower_formula
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Field K]
  [Field L]
  [Algebra K L]
  [CommRing B]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [IsDedekindDomain B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  {P : Ideal B}
  [IsGalois K L]
  [FiniteDimensional K L]
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  {P_E : Ideal C_E}
  [P_E.IsMaximal]
  [P_E.LiesOver p]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [P.LiesOver p]
  [P.LiesOver P_E]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (hP_E : P_E ≠ ⊥) :
-- imply
  Ideal.ramificationIdx p P_E * Nat.card (P.inertia (↥E.fixingSubgroup)) = Nat.card (P.inertia (L ≃ₐ[K] L)) := by
-- proof
  have h_full := Ideal.card_inertia_eq_ramificationIdxIn (G := (L ≃ₐ[K] L)) p hp P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (L ≃ₐ[K] L)] at h_full
  have h_sub := Ideal.card_inertia_eq_ramificationIdxIn (G := ↥E.fixingSubgroup) P_E hP_E P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P_E P ↥E.fixingSubgroup] at h_sub
  have h_tower := Ideal.ramificationIdx_algebra_tower' p P_E P
  rw [h_full, h_sub, h_tower]

/--
[ramificationIdx_mul_card_inertia_subgroupOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma ramificationIdx_mul_card_inertia_subgroupOf
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Field K]
  [Field L]
  [Algebra K L]
  [CommRing B]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [IsDedekindDomain B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  {P : Ideal B}
  [IsGalois K L]
  [FiniteDimensional K L]
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  {P_E : Ideal C_E}
  [P_E.IsMaximal]
  [P_E.LiesOver p]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [P.LiesOver p]
  [P.LiesOver P_E]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (hP_E : P_E ≠ ⊥) :
-- imply
  Ideal.ramificationIdx p P_E * Nat.card ((P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup) = Nat.card (P.inertia (L ≃ₐ[K] L)) := by
-- proof
  rw [show (P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup =
    P.inertia E.fixingSubgroup from
    AddSubgroup.subgroupOf_inertia P.toAddSubgroup E.fixingSubgroup]
  exact card_inertia_tower_formula P p E C_E P_E hp hP_E

/--
[ramificationIdx_eq_one_iff_inertia_le_fixingSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma ramificationIdx_eq_one_iff_inertia_le_fixingSubgroup
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [IsDedekindDomain B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  {P : Ideal B}
  [IsGalois K L]
  [FiniteDimensional K L]
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  {P_E : Ideal C_E}
  [P_E.IsMaximal]
  [P_E.LiesOver p]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [P.LiesOver p]
  [P.LiesOver P_E]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (hP_E : P_E ≠ ⊥) :
-- imply
  Ideal.ramificationIdx p P_E = 1 ↔ P.inertia (L ≃ₐ[K] L) ≤ E.fixingSubgroup := by
-- proof
  have htower := ramificationIdx_mul_card_inertia_subgroupOf P p E C_E P_E hp hP_E
  constructor
  ·
    intro he
    rw [he, one_mul] at htower
    exact Subgroup.le_of_card_subgroupOf_eq' htower
  ·
    intro hle
    have hcard_eq : Nat.card ((P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup) =
      Nat.card (P.inertia (L ≃ₐ[K] L)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hcard_eq] at htower
    exact mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp Nat.card_pos)
      (htower.trans (one_mul _).symm)

/--
[e_eq_one_iff_le_inertiaField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma e_eq_one_iff_le_inertiaField
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [IsDedekindDomain B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  {P : Ideal B}
  [IsGalois K L]
  [FiniteDimensional K L]
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  {P_E : Ideal C_E}
  [P_E.IsMaximal]
  [P_E.LiesOver p]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [P.LiesOver p]
  [P.LiesOver P_E]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (hP_E : P_E ≠ ⊥) :
-- imply
  Ideal.ramificationIdx p P_E = 1 ↔ E ≤ IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L)) := by
-- proof
  rw [ramificationIdx_eq_one_iff_inertia_le_fixingSubgroup K L P p E C_E P_E hp hP_E]
  exact (IntermediateField.le_iff_le (P.inertia (L ≃ₐ[K] L)) E).symm
omit [Algebra B L] in
set_option maxHeartbeats 400000 in

/--
[ef_mul_card_stabilizer_subgroupOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma ef_mul_card_stabilizer_subgroupOf
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [IsDedekindDomain B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  {P : Ideal B}
  [IsGalois K L]
  [FiniteDimensional K L]
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  {P_E : Ideal C_E}
  [P_E.IsMaximal]
  [P_E.LiesOver p]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [P.LiesOver p]
  [P.LiesOver P_E]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (hP_E : P_E ≠ ⊥) :
-- imply
  (Ideal.ramificationIdx p P_E * Ideal.inertiaDeg p P_E) * Nat.card ((@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _ Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup) = Nat.card (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _ Ideal.pointwiseMulSemiringAction.toMulAction P) := by
-- proof
  rw [show (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
    Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup =
    @MulAction.stabilizer (↥E.fixingSubgroup) (Ideal B) _
      Ideal.pointwiseMulSemiringAction.toMulAction P from by
    ext ⟨h, hH⟩
    simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rfl]
  have h_full := Ideal.card_stabilizer_eq (G := (L ≃ₐ[K] L)) p hp P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg p P (L ≃ₐ[K] L)] at h_full
  have h_sub := Ideal.card_stabilizer_eq (G := ↥E.fixingSubgroup) P_E hP_E P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P_E P ↥E.fixingSubgroup,
    Ideal.inertiaDegIn_eq_inertiaDeg P_E P ↥E.fixingSubgroup] at h_sub
  have h_e_tower := Ideal.ramificationIdx_algebra_tower' p P_E P
  have h_f_tower := Ideal.inertiaDeg_algebra_tower p P_E P
  rw [h_full, h_sub, h_e_tower, h_f_tower]
  ring

/--
[ef_eq_one_iff_stabilizer_le_fixingSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma ef_eq_one_iff_stabilizer_le_fixingSubgroup
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [IsDedekindDomain B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  {P : Ideal B}
  [IsGalois K L]
  [FiniteDimensional K L]
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  {P_E : Ideal C_E}
  [P_E.IsMaximal]
  [P_E.LiesOver p]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [P.LiesOver p]
  [P.LiesOver P_E]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (hP_E : P_E ≠ ⊥) :
-- imply
  (Ideal.ramificationIdx p P_E = 1 ∧ Ideal.inertiaDeg p P_E = 1) ↔ (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _ Ideal.pointwiseMulSemiringAction.toMulAction P) ≤ E.fixingSubgroup := by
-- proof
  have htower := ef_mul_card_stabilizer_subgroupOf K L P p E C_E P_E hp hP_E
  constructor
  ·
    intro ⟨he, hf⟩
    rw [he, hf, mul_one, one_mul] at htower
    exact Subgroup.le_of_card_subgroupOf_eq' htower
  ·
    intro hle
    have hcard_eq : Nat.card ((@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
      Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup) =
      Nat.card (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hcard_eq] at htower
    have hef : Ideal.ramificationIdx p P_E * Ideal.inertiaDeg p P_E = 1 :=
      mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp Nat.card_pos)
        (htower.trans (one_mul _).symm)
    exact mul_eq_one.mp hef

/--
[ef_eq_one_iff_le_decompositionField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma ef_eq_one_iff_le_decompositionField
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [IsDedekindDomain B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  {P : Ideal B}
  [IsGalois K L]
  [FiniteDimensional K L]
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  {P_E : Ideal C_E}
  [P_E.IsMaximal]
  [P_E.LiesOver p]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [P.LiesOver p]
  [P.LiesOver P_E]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (hP_E : P_E ≠ ⊥) :
-- imply
  (Ideal.ramificationIdx p P_E = 1 ∧ Ideal.inertiaDeg p P_E = 1) ↔ E ≤ IntermediateField.fixedField (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _ Ideal.pointwiseMulSemiringAction.toMulAction P) := by
-- proof
  rw [IntermediateField.le_iff_le]
  exact ef_eq_one_iff_stabilizer_le_fixingSubgroup K L P p E C_E P_E hp hP_E

/--
[e_ef_eq_one_iff_le_inertiaField_decompositionField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma e_ef_eq_one_iff_le_inertiaField_decompositionField
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [IsDedekindDomain B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  {P : Ideal B}
  [IsGalois K L]
  [FiniteDimensional K L]
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  {P_E : Ideal C_E}
  [P_E.IsMaximal]
  [P_E.LiesOver p]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [P.LiesOver p]
  [P.LiesOver P_E]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (hP_E : P_E ≠ ⊥) :
-- imply
  (Ideal.ramificationIdx p P_E = 1 ↔ E ≤ IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L))) ∧ ((Ideal.ramificationIdx p P_E = 1 ∧ Ideal.inertiaDeg p P_E = 1) ↔ E ≤ IntermediateField.fixedField (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _ Ideal.pointwiseMulSemiringAction.toMulAction P)) :=
-- proof
  ⟨e_eq_one_iff_le_inertiaField K L P p E C_E P_E hp hP_E,
    ef_eq_one_iff_le_decompositionField K L P p E C_E P_E hp hP_E⟩
end UnramifiedSplitCharacterization
section InertiaDecompositionNormality
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]

/--
[inertiaGroup_normal_in_decompositionGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma inertiaGroup_normal_in_decompositionGroup
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]
  {Q : Ideal B}
  [Q.IsPrime] :
-- imply
  ((Q.inertia G).subgroupOf (MulAction.stabilizer G Q)).Normal :=
-- proof
  inferInstance
end InertiaDecompositionNormality
section GaloisInertiaDecompositionFields
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L]

/--
[isGalois_inertiaField_normalClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma isGalois_inertiaField_normalClosure
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [CommRing B]
  [IsDedekindDomain B]
  [Algebra B L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  {P : Ideal B} :
-- imply
  IsGalois K (IntermediateField.fixedField (Subgroup.normalClosure (↑(P.inertia (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)))) := by
-- proof
  haveI : (Subgroup.normalClosure (↑(P.inertia (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L))).Normal :=
    Subgroup.normalClosure_normal
  exact IsGalois.of_fixedField_normal_subgroup _

/--
[isGalois_decompositionField_normalClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma isGalois_decompositionField_normalClosure
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [CommRing B]
  [IsDedekindDomain B]
  [Algebra B L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  {P : Ideal B} :
-- imply
  IsGalois K (IntermediateField.fixedField (Subgroup.normalClosure (↑(MulAction.stabilizer (L ≃ₐ[K] L) P) : Set (L ≃ₐ[K] L)))) := by
-- proof
  haveI : (Subgroup.normalClosure
    (↑(MulAction.stabilizer (L ≃ₐ[K] L) P) : Set (L ≃ₐ[K] L))).Normal :=
    Subgroup.normalClosure_normal
  exact IsGalois.of_fixedField_normal_subgroup _

/--
[normalClosure_le_iff_forall_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma normalClosure_le_iff_forall_conj
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Group G]
  {H N : Subgroup G} :
-- imply
  Subgroup.normalClosure (↑H : Set G) ≤ N ↔ ∀ g : G, H.map (MulAut.conj g).toMonoidHom ≤ N := by
-- proof
  simp only [Subgroup.normalClosure, Subgroup.closure_le]
  constructor
  · intro hle g x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    apply hle
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨h, hh, isConj_iff.mpr ⟨g, rfl⟩⟩
  · intro hall x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj⟩ := hx
    rw [isConj_iff] at hconj
    obtain ⟨g, rfl⟩ := hconj
    exact hall g (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)

/--
[normalClosure_stabilizer_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma normalClosure_stabilizer_le_iff
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Group G]
  [MulAction G α]
  {a : α}
  {N : Subgroup G} :
-- imply
  Subgroup.normalClosure (↑(MulAction.stabilizer G a) : Set G) ≤ N ↔ ∀ g : G, MulAction.stabilizer G (g • a) ≤ N := by
-- proof
  rw [normalClosure_le_iff_forall_conj]
  simp_rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]

/--
[Ideal.IsMaximal.smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma Ideal.IsMaximal.smul
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Group G]
  [CommRing B]
  [MulSemiringAction G B]
  {P : Ideal B}
  {g : G}
-- given
  (hP : P.IsMaximal) :
-- imply
  (g • P).IsMaximal := by
-- proof
  rw [Ideal.pointwise_smul_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ (MulSemiringAction.toRingAut G B g).symm.surjective

/--
[inertia_smul_eq_inertia_map_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma inertia_smul_eq_inertia_map_conj
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Group G]
  [CommRing B]
  [MulSemiringAction G B]
  {P : Ideal B}
  {σ : G} :
-- imply
  (σ • P).inertia G = (P.inertia G).map (MulAut.conj σ).toMonoidHom := by
-- proof
  ext g
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hg
    refine ⟨σ⁻¹ * g * σ, ?_, by group⟩
    intro x
    have h1 := hg (σ • x)
    have key : g • (σ • x) - σ • x = σ • ((σ⁻¹ * g * σ) • x - x) := by
      simp [mul_smul, smul_sub]
    rw [key] at h1
    change σ • _ ∈ (σ • P : Ideal B) at h1
    rwa [Ideal.smul_mem_pointwise_smul_iff] at h1
  · rintro ⟨h, hh, rfl⟩
    intro x
    have h1 := hh (σ⁻¹ • x)
    have key : (σ * h * σ⁻¹) • x - x = σ • (h • (σ⁻¹ • x) - σ⁻¹ • x) := by
      simp [mul_smul, smul_sub]
    rw [key]
    change σ • _ ∈ (σ • P : Ideal B)
    rwa [Ideal.smul_mem_pointwise_smul_iff]

/--
[normalClosure_inertia_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma normalClosure_inertia_le_iff
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Group G]
  [CommRing B]
  [MulSemiringAction G B]
  {P : Ideal B}
  {N : Subgroup G} :
-- imply
  Subgroup.normalClosure (↑(P.inertia G) : Set G) ≤ N ↔ ∀ σ : G, (σ • P).inertia G ≤ N := by
-- proof
  rw [normalClosure_le_iff_forall_conj]
  simp_rw [inertia_smul_eq_inertia_map_conj]

/--
[unramified_all_primes_iff_le_inertiaField_normalClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma unramified_all_primes_iff_le_inertiaField_normalClosure
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [CommRing B]
  [IsDedekindDomain B]
  [Algebra B L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  [Algebra.IsIntegral A B]
  [SMulCommClass (L ≃ₐ[K] L) A B]
  {P : Ideal B}
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  [P.LiesOver p]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (h_sep_A : ∀ (P' : Ideal B) [P'.IsMaximal] [P'.LiesOver p], Algebra.IsSeparable (A ⧸ p) (B ⧸ P'))
  (h_sep_C : ∀ (Q' : Ideal C_E) (P' : Ideal B) [Q'.IsMaximal] [P'.IsMaximal] [Q'.LiesOver p] [P'.LiesOver Q'], Algebra.IsSeparable (C_E ⧸ Q') (B ⧸ P'))
  (h_exists_smul : ∀ (Q' : Ideal C_E) [Q'.IsMaximal] [Q'.LiesOver p], ∃ σ : L ≃ₐ[K] L, (σ • P).LiesOver Q')
  (hQ_ne_bot : ∀ (Q' : Ideal C_E) [Q'.IsMaximal] [Q'.LiesOver p], Q' ≠ ⊥) :
-- imply
  (∀ (Q : Ideal C_E) [Q.IsMaximal] [Q.LiesOver p], Ideal.ramificationIdx p Q = 1) ↔ E ≤ IntermediateField.fixedField (Subgroup.normalClosure (↑(P.inertia (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L))) := by
-- proof
  rw [IntermediateField.le_iff_le]
  rw [normalClosure_inertia_le_iff]
  constructor
  ·
    intro hall σ
    haveI : (σ • P).IsMaximal := Ideal.IsMaximal.smul ‹P.IsMaximal› σ
    haveI : (σ • P).LiesOver p := Ideal.LiesOver.smul σ
    haveI : Algebra.IsIntegral C_E B := Algebra.IsIntegral.tower_top (R := A)
    set Q_σ := Ideal.comap (algebraMap C_E B) (σ • P)
    haveI : Q_σ.IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (σ • P)
    haveI : Q_σ.LiesOver p := Ideal.under_liesOver_of_liesOver C_E (σ • P) p
    haveI : (σ • P).LiesOver Q_σ := ⟨rfl⟩
    haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ (σ • P)) := h_sep_A (σ • P)
    haveI : Algebra.IsSeparable (C_E ⧸ Q_σ) (B ⧸ (σ • P)) := h_sep_C Q_σ (σ • P)
    have hQ_ne := hQ_ne_bot Q_σ
    have hQ := hall Q_σ
    rw [e_eq_one_iff_le_inertiaField K L (σ • P) p E C_E Q_σ hp hQ_ne] at hQ
    exact (IntermediateField.le_iff_le ((σ • P).inertia (L ≃ₐ[K] L)) E).mp hQ
  ·
    intro hall Q _ _
    obtain ⟨σ, hσ_over⟩ := h_exists_smul Q
    haveI : (σ • P).IsMaximal := Ideal.IsMaximal.smul ‹P.IsMaximal› σ
    haveI : (σ • P).LiesOver p := Ideal.LiesOver.smul σ
    haveI : (σ • P).LiesOver Q := hσ_over
    haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ (σ • P)) := h_sep_A (σ • P)
    haveI : Algebra.IsSeparable (C_E ⧸ Q) (B ⧸ (σ • P)) := h_sep_C Q (σ • P)
    have hQ_ne := hQ_ne_bot Q
    rw [e_eq_one_iff_le_inertiaField K L (σ • P) p E C_E Q hp hQ_ne]
    apply (IntermediateField.le_iff_le ((σ • P).inertia (L ≃ₐ[K] L)) E).mpr
    exact hall σ

/--
[splitsCompletely_all_primes_iff_le_decompositionField_normalClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma splitsCompletely_all_primes_iff_le_decompositionField_normalClosure
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [CommRing B]
  [IsDedekindDomain B]
  [Algebra B L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [FaithfulSMul (L ≃ₐ[K] L) B]
  [CommRing A]
  [IsDedekindDomain A]
  [Algebra A B]
  [Algebra.IsIntegral A B]
  [SMulCommClass (L ≃ₐ[K] L) A B]
  {P : Ideal B}
  [P.IsMaximal]
  {p : Ideal A}
  [p.IsMaximal]
  [P.LiesOver p]
  {E : IntermediateField K L}
  {C_E : Type*}
  [CommRing C_E]
  [IsDedekindDomain C_E]
  [Algebra A C_E]
  [Algebra C_E B]
  [IsScalarTower A C_E B]
  [Algebra A ↥E]
  [Algebra C_E ↥E]
  [IsIntegralClosure C_E A ↥E]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Finite C_E B]
  [Module.IsTorsionFree C_E B]
  [Module.IsTorsionFree A C_E]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
-- given
  (hp : p ≠ ⊥)
  (h_sep_A : ∀ (P' : Ideal B) [P'.IsMaximal] [P'.LiesOver p], Algebra.IsSeparable (A ⧸ p) (B ⧸ P'))
  (h_sep_C : ∀ (Q' : Ideal C_E) (P' : Ideal B) [Q'.IsMaximal] [P'.IsMaximal] [Q'.LiesOver p] [P'.LiesOver Q'], Algebra.IsSeparable (C_E ⧸ Q') (B ⧸ P'))
  (h_exists_smul : ∀ (Q' : Ideal C_E) [Q'.IsMaximal] [Q'.LiesOver p], ∃ σ : L ≃ₐ[K] L, (σ • P).LiesOver Q')
  (hQ_ne_bot : ∀ (Q' : Ideal C_E) [Q'.IsMaximal] [Q'.LiesOver p], Q' ≠ ⊥) :
-- imply
  (∀ (Q : Ideal C_E) [Q.IsMaximal] [Q.LiesOver p], Ideal.ramificationIdx p Q = 1 ∧ Ideal.inertiaDeg p Q = 1) ↔ E ≤ IntermediateField.fixedField (Subgroup.normalClosure (↑(MulAction.stabilizer (L ≃ₐ[K] L) P) : Set (L ≃ₐ[K] L))) := by
-- proof
  rw [IntermediateField.le_iff_le]
  rw [normalClosure_stabilizer_le_iff]
  constructor
  ·
    intro hall σ
    haveI : (σ • P).IsMaximal := Ideal.IsMaximal.smul ‹P.IsMaximal› σ
    haveI : (σ • P).LiesOver p := Ideal.LiesOver.smul σ
    haveI : Algebra.IsIntegral C_E B := Algebra.IsIntegral.tower_top (R := A)
    set Q_σ := Ideal.comap (algebraMap C_E B) (σ • P)
    haveI : Q_σ.IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (σ • P)
    haveI : Q_σ.LiesOver p := Ideal.under_liesOver_of_liesOver C_E (σ • P) p
    haveI : (σ • P).LiesOver Q_σ := ⟨rfl⟩
    haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ (σ • P)) := h_sep_A (σ • P)
    haveI : Algebra.IsSeparable (C_E ⧸ Q_σ) (B ⧸ (σ • P)) := h_sep_C Q_σ (σ • P)
    have hQ_ne := hQ_ne_bot Q_σ
    have hQ := hall Q_σ
    exact (ef_eq_one_iff_stabilizer_le_fixingSubgroup K L (σ • P) p E C_E Q_σ hp hQ_ne).mp hQ
  ·
    intro hall Q _ _
    obtain ⟨σ, hσ_over⟩ := h_exists_smul Q
    haveI : (σ • P).IsMaximal := Ideal.IsMaximal.smul ‹P.IsMaximal› σ
    haveI : (σ • P).LiesOver p := Ideal.LiesOver.smul σ
    haveI : (σ • P).LiesOver Q := hσ_over
    haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ (σ • P)) := h_sep_A (σ • P)
    haveI : Algebra.IsSeparable (C_E ⧸ Q) (B ⧸ (σ • P)) := h_sep_C Q (σ • P)
    have hQ_ne := hQ_ne_bot Q
    rw [show (Ideal.ramificationIdx p Q = 1 ∧ Ideal.inertiaDeg p Q = 1) ↔
      MulAction.stabilizer (L ≃ₐ[K] L) (σ • P) ≤ E.fixingSubgroup from
      ef_eq_one_iff_stabilizer_le_fixingSubgroup K L (σ • P) p E C_E Q hp hQ_ne]
    exact hall σ
end GaloisInertiaDecompositionFields
section FrobeniusElement
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[isFrobeniusElement_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma isFrobeniusElement_one
  [CommRing B]
  {Q : Ideal B} :
-- imply
  IsFrobeniusElement G 1 Q 1 := by
-- proof
  intro x; simp [one_smul, pow_one, sub_self, Q.zero_mem]

/--
[frobeniusElement_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobeniusElement_spec
  [CommRing B]
  {Q : Ideal B}
  {q : ℕ}
-- given
  (hexists : ∃! σ : G, IsFrobeniusElement G σ Q q) :
-- imply
  IsFrobeniusElement G (frobeniusElement G Q q hexists) Q q :=
-- proof
  hexists.choose_spec.1

/--
[frobeniusElement_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobeniusElement_unique
  [CommRing B]
  {Q : Ideal B}
  {q : ℕ}
  {σ : G}
-- given
  (hexists : ∃! σ : G, IsFrobeniusElement G σ Q q)
  (hσ : IsFrobeniusElement G σ Q q) :
-- imply
  σ = frobeniusElement G Q q hexists :=
-- proof
  hexists.choose_spec.2 σ hσ
end FrobeniusElement
section FrobeniusExistsUnique
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Finite G] [Algebra.IsInvariant A B G]

/--
[isFrobeniusElement_eq_isArithFrobAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma isFrobeniusElement_eq_isArithFrobAt
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {σ : G}
  {Q : Ideal B} :
-- imply
  IsFrobeniusElement G σ Q (Nat.card (A ⧸ Q.under A)) ↔ IsArithFrobAt A σ Q :=
-- proof
  Iff.rfl

/--
[frobenius_existsUnique_of_inertia_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobenius_existsUnique_of_inertia_eq_bot
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {Q : Ideal B}
  [Q.IsPrime]
  [Finite (B ⧸ Q)]
-- given
  (hunr : Q.inertia G = ⊥) :
-- imply
  ∃! σ : G, IsFrobeniusElement G σ Q (Nat.card (A ⧸ Q.under A)) := by
-- proof
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant A G Q
  refine ⟨σ, hσ, fun σ' hσ' => ?_⟩
  have hmem : σ' * σ⁻¹ ∈ Q.inertia G := IsArithFrobAt.mul_inv_mem_inertia hσ' hσ
  rwa [hunr, Subgroup.mem_bot, mul_inv_eq_one] at hmem
end FrobeniusExistsUnique
section FrobeniusConjugacy
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[isFrobeniusElement_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma isFrobeniusElement_conj
  [CommRing B]
  {σ τ : G}
  {Q : Ideal B}
  {q : ℕ}
-- given
  (hσ : IsFrobeniusElement G σ Q q) :
-- imply
  IsFrobeniusElement G (τ * σ * τ⁻¹) (τ • Q) q := by
-- proof
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, smul_pow']
  have heq : τ⁻¹ • (τ * σ * τ⁻¹) • x = σ • (τ⁻¹ • x) := by
    simp only [smul_smul]; congr 1; group
  rw [heq]
  exact hσ (τ⁻¹ • x)

/--
[frobeniusElement_conjugate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobeniusElement_conjugate
  [CommRing B]
  {Q : Ideal B}
  {q : ℕ}
  {τ : G}
-- given
  (hexists_Q : ∃! σ : G, IsFrobeniusElement G σ Q q)
  (hexists_tQ : ∃! σ : G, IsFrobeniusElement G σ (τ • Q) q) :
-- imply
  frobeniusElement G (τ • Q) q hexists_tQ = τ * frobeniusElement G Q q hexists_Q * τ⁻¹ := by
-- proof
  symm
  apply hexists_tQ.choose_spec.2
  exact isFrobeniusElement_conj G (frobeniusElement_spec G Q q hexists_Q)
end FrobeniusConjugacy
section FrobeniusClassDef
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[frobeniusClass_eq_of_conjugate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobeniusClass_eq_of_conjugate
  [CommRing B]
  {Q : Ideal B}
  {q : ℕ}
  {τ : G}
-- given
  (hexists_Q : ∃! σ : G, IsFrobeniusElement G σ Q q)
  (hexists_tQ : ∃! σ : G, IsFrobeniusElement G σ (τ • Q) q) :
-- imply
  frobeniusClass G (τ • Q) q hexists_tQ = frobeniusClass G Q q hexists_Q := by
-- proof
  unfold frobeniusClass
  rw [frobeniusElement_conjugate G hexists_Q τ hexists_tQ]
  simp only [ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_iff.mpr ⟨τ⁻¹, by group⟩
end FrobeniusClassDef
section ArtinSymbolDef
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[artinSymbol_eq_one_iff_frobeniusCondition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma artinSymbol_eq_one_iff_frobeniusCondition
  [CommRing B]
  {Q : Ideal B}
  {q : ℕ}
-- given
  (hexists : ∃! σ : G, IsFrobeniusElement G σ Q q) :
-- imply
  frobeniusElement G Q q hexists = 1 ↔ ∀ x : B, (x - x ^ q) ∈ Q := by
-- proof
  constructor
  · intro h x
    have := frobeniusElement_spec G Q q hexists x
    rwa [h, one_smul] at this
  · intro h
    have h1 : IsFrobeniusElement G 1 Q q := fun x => by simpa [one_smul] using h x
    exact (frobeniusElement_unique G Q q hexists 1 h1).symm

/--
[artinSymbol_eq_one_iff_decompositionGroup_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma artinSymbol_eq_one_iff_decompositionGroup_trivial
  [CommRing B]
  {Q : Ideal B}
  {q : ℕ}
-- given
  (hexists : ∃! σ : G, IsFrobeniusElement G σ Q q)
  (hmem : frobeniusElement G Q q hexists ∈ MulAction.stabilizer G Q)
  (hgen : ∀ g, g ∈ MulAction.stabilizer G Q → ∃ n : ℕ, g = frobeniusElement G Q q hexists ^ n) :
-- imply
  frobeniusElement G Q q hexists = 1 ↔ MulAction.stabilizer G Q = ⊥ := by
-- proof
  constructor
  · intro h
    ext g
    simp only [Subgroup.mem_bot]
    constructor
    · intro hg
      obtain ⟨n, hn⟩ := hgen g hg
      rw [hn, h, one_pow]
    · intro hg; rw [hg]; exact (MulAction.stabilizer G Q).one_mem
  · intro h
    have hmem' : frobeniusElement G Q q hexists ∈ (⊥ : Subgroup G) := h ▸ hmem
    rwa [Subgroup.mem_bot] at hmem'
section UnramifiedFrobeniusDataDef
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[decompositionGroup_trivial_iff_splitsCompletely](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma decompositionGroup_trivial_iff_splitsCompletely
  [CommRing A]
  [IsDedekindDomain A]
  {P : Ideal B}
  [P.LiesOver p]
  [P.IsMaximal]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
-- given
  (hp : p ≠ ⊥) :
-- imply
  MulAction.stabilizer G P = ⊥ ↔ (primesOver p B).ncard = Nat.card G := by
-- proof
  have hef : Nat.card (MulAction.stabilizer G P) = ramificationIdxIn p B * inertiaDegIn p B :=
    Ideal.card_stabilizer_eq p hp P
  have hefg : (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G :=
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G
  rw [← Subgroup.card_eq_one]
  constructor
  ·
    intro h
    rw [hef] at h
    rwa [h, mul_one] at hefg
  ·
    intro h
    rw [hef]
    rw [← h] at hefg
    have hg_pos : (primesOver p B).ncard ≠ 0 := by
      rw [h]; exact Nat.card_pos.ne'
    have : (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) =
      (primesOver p B).ncard * 1 := by rw [mul_one]; exact hefg
    exact mul_left_cancel₀ hg_pos this

/--
[artinSymbol_trivial_iff_splitsCompletely](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma artinSymbol_trivial_iff_splitsCompletely
  [CommRing A]
  [IsDedekindDomain A]
  {P : Ideal B}
  [P.LiesOver p]
  [P.IsMaximal]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  {q : ℕ}
-- given
  (hp : p ≠ ⊥)
  (hexists : ∃! σ : G, IsFrobeniusElement G σ P q)
  (hmem : frobeniusElement G P q hexists ∈ MulAction.stabilizer G P)
  (hgen : ∀ g, g ∈ MulAction.stabilizer G P → ∃ n : ℕ, g = frobeniusElement G P q hexists ^ n) :
-- imply
  frobeniusElement G P q hexists = 1 ↔ (primesOver p B).ncard = Nat.card G := by
-- proof
  rw [artinSymbol_eq_one_iff_decompositionGroup_trivial G hexists hmem hgen]
  exact decompositionGroup_trivial_iff_splitsCompletely G hp P

/--
[artinSymbol_trivial_iff_splitsCompletely'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma artinSymbol_trivial_iff_splitsCompletely'
  [CommRing A]
  [IsDedekindDomain A]
  {P : Ideal B}
  [P.LiesOver p]
  [P.IsMaximal]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  {q : ℕ}
-- given
  (hp : p ≠ ⊥)
  (hdata : UnramifiedFrobeniusData G P q) :
-- imply
  frobeniusElement G P q hdata.unique_exists = 1 ↔ (primesOver p B).ncard = Nat.card G :=
-- proof
  artinSymbol_trivial_iff_splitsCompletely G hp P
    hdata.unique_exists hdata.mem_stabilizer hdata.generates_stabilizer
section FrobeniusTower
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[Ideal.pow_sub_pow_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma Ideal.pow_sub_pow_mem
  [CommRing B]
  [CommRing R]
  {I : Ideal R}
  {a b : R}
  {n : ℕ}
-- given
  (h : a - b ∈ I) :
-- imply
  a ^ n - b ^ n ∈ I := by
-- proof
  have hq : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := Ideal.Quotient.eq.mpr h
  exact Ideal.Quotient.eq.mp (by simp only [map_pow, hq])

/--
[isFrobeniusElement_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma isFrobeniusElement_pow
  [CommRing B]
  {σ : G}
  {Q : Ideal B}
  {q : ℕ}
  {f : ℕ}
-- given
  (hσ : IsFrobeniusElement G σ Q q) :
-- imply
  IsFrobeniusElement G (σ ^ f) Q (q ^ f) := by
-- proof
  induction f with
  | zero => intro x; simp [pow_zero, one_smul, sub_self, Q.zero_mem]
  | succ n ih =>
    intro x
    rw [pow_succ, mul_smul]
    have h1 := ih (σ • x)
    have h2 : (σ • x) ^ (q ^ n) - (x ^ q) ^ (q ^ n) ∈ Q :=
      Ideal.pow_sub_pow_mem Q (q ^ n) (hσ x)
    have htele : σ ^ n • σ • x - x ^ q ^ (n + 1) =
      (σ ^ n • σ • x - (σ • x) ^ q ^ n) + ((σ • x) ^ q ^ n - (x ^ q) ^ q ^ n) := by ring
    rw [htele]
    exact Q.add_mem h1 h2

/--
[artinSymbol_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma artinSymbol_tower
  [CommRing B]
  {Q : Ideal B}
  {q f : ℕ}
-- given
  (hexists_q : ∃! σ : G, IsFrobeniusElement G σ Q q)
  (hexists_qf : ∃! σ : G, IsFrobeniusElement G σ Q (q ^ f)) :
-- imply
  frobeniusElement G Q (q ^ f) hexists_qf = (frobeniusElement G Q q hexists_q) ^ f :=
-- proof
  (frobeniusElement_unique G Q (q ^ f) hexists_qf _ <|
    isFrobeniusElement_pow G (frobeniusElement_spec G Q q hexists_q) f).symm
end FrobeniusTower
section FrobeniusRestriction
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[isFrobeniusElement_restriction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma isFrobeniusElement_restriction
  [CommRing B]
  [CommRing C]
  {H : Type*}
  [Group H]
  [MulSemiringAction H C]
  {ι : C →+* B}
  {ρ : G →* H}
  {σ : G}
  {Q : Ideal B}
  {q : ℕ}
-- given
  (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
  (hσ : IsFrobeniusElement G σ Q q) :
-- imply
  IsFrobeniusElement H (ρ σ) (Q.comap ι) q := by
-- proof
  intro c
  rw [Ideal.mem_comap]
  have : ι (ρ σ • c - c ^ q) = σ • ι c - (ι c) ^ q := by
    rw [map_sub, map_pow, hcompat]
  rw [this]
  exact hσ (ι c)

/--
[frobeniusElement_restriction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobeniusElement_restriction
  [CommRing B]
  [CommRing C]
  {H : Type*}
  [Group H]
  [MulSemiringAction H C]
  {ι : C →+* B}
  {ρ : G →* H}
  {Q : Ideal B}
  {q : ℕ}
-- given
  (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
  (hexists_G : ∃! σ : G, IsFrobeniusElement G σ Q q)
  (hexists_H : ∃! τ : H, IsFrobeniusElement H τ (Q.comap ι) q) :
-- imply
  frobeniusElement H (Q.comap ι) q hexists_H = ρ (frobeniusElement G Q q hexists_G) := by
-- proof
  symm
  exact frobeniusElement_unique H (Q.comap ι) q hexists_H _ <|
    isFrobeniusElement_restriction G H ι ρ hcompat
      (frobeniusElement_spec G Q q hexists_G)
end FrobeniusRestriction
section FrobeniusInertiaHelpers
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[isFrobeniusElement_mul_inv_mem_inertia](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma isFrobeniusElement_mul_inv_mem_inertia
  [CommRing B]
  {σ σ' : G}
  {Q : Ideal B}
  {n : ℕ}
-- given
  (h0 : IsFrobeniusElement G σ Q n)
  (h1 : IsFrobeniusElement G σ' Q n) :
-- imply
  σ * σ'⁻¹ ∈ Q.inertia G := by
-- proof
  intro x
  simpa [mul_smul] using Q.sub_mem (h1 (σ'⁻¹ • x)) (h2 (σ'⁻¹ • x))

/--
[frobenius_existsUnique_of_exists_of_inertia_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobenius_existsUnique_of_exists_of_inertia_eq_bot
  [CommRing B]
  {Q : Ideal B}
  {n : ℕ}
  {σ : G}
-- given
  (hσ : IsFrobeniusElement G σ Q n)
  (hunr : Q.inertia G = ⊥) :
-- imply
  ∃! τ : G, IsFrobeniusElement G τ Q n := by
-- proof
  refine ⟨σ, hσ, fun σ' hσ' => ?_⟩
  have hmem : σ' * σ⁻¹ ∈ Q.inertia G :=
    isFrobeniusElement_mul_inv_mem_inertia G hσ' hσ
  rwa [hunr, Subgroup.mem_bot, mul_inv_eq_one] at hmem
end FrobeniusInertiaHelpers
section FrobeniusTowerAndRestriction
variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

/--
[frobeniusElement_tower_and_restriction_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobeniusElement_tower_and_restriction_abstract
  [CommRing B]
  [CommRing C]
  {H : Type*}
  [Group H]
  [MulSemiringAction H C]
  {ι : C →+* B}
  {ρ : G →* H}
  {Q : Ideal B}
  {q f : ℕ}
-- given
  (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
  (hexists_q : ∃! σ : G, IsFrobeniusElement G σ Q q)
  (hexists_qf : ∃! σ : G, IsFrobeniusElement G σ Q (q ^ f))
  (hexists_H : ∃! τ : H, IsFrobeniusElement H τ (Q.comap ι) q) :
-- imply
  (frobeniusElement G Q (q ^ f) hexists_qf = (frobeniusElement G Q q hexists_q) ^ f) ∧ (frobeniusElement H (Q.comap ι) q hexists_H = ρ (frobeniusElement G Q q hexists_q)) :=
-- proof
  ⟨artinSymbol_tower G hexists_q hexists_qf,
    frobeniusElement_restriction G H ι ρ hcompat hexists_q hexists_H⟩

/--
[frobeniusElement_tower_and_restriction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma frobeniusElement_tower_and_restriction
  [CommRing B]
  [CommRing A]
  [Algebra A B]
  [SMulCommClass G A B]
  [Finite G]
  [Algebra.IsInvariant A B G]
  [CommRing C]
  {H : Type*}
  [Group H]
  [MulSemiringAction H C]
  [Algebra A C]
  [SMulCommClass H A C]
  [Finite H]
  [Algebra.IsInvariant A C H]
  {ι : C →+* B}
  {ρ : G →* H}
  {Q : Ideal B}
  [Q.IsPrime]
  [Finite (B ⧸ Q)]
  [(Q.comap ι).IsPrime]
  [Finite (C ⧸ Q.comap ι)]
  {f : ℕ}
-- given
  (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
  (hunr : Q.inertia G = ⊥)
  (hunr_H : (Q.comap ι).inertia H = ⊥)
  (hunder : (Q.comap ι).under A = Q.under A) :
-- imply
  let q := Nat.card (A ⧸ Q.under A) let hexists_q := frobenius_existsUnique_of_inertia_eq_bot G Q hunr let hexists_qf := frobenius_existsUnique_of_exists_of_inertia_eq_bot G (isFrobeniusElement_pow G (frobeniusElement_spec G Q q hexists_q) f) hunr (frobeniusElement G Q (q ^ f) hexists_qf = (frobeniusElement G Q q hexists_q) ^ f) ∧ ∃ hexists_H : ∃! τ : H, IsFrobeniusElement H τ (Q.comap ι) q, (frobeniusElement H (Q.comap ι) q hexists_H = ρ (frobeniusElement G Q q hexists_q)) := by
-- proof
  intro q hexists_q hexists_qf
  have hexists_H_raw := frobenius_existsUnique_of_inertia_eq_bot (A := A) H (Q.comap ι) hunr_H
  have hq_eq : Nat.card (A ⧸ (Q.comap ι).under A) = q := by rw [hunder]
  have hexists_H : ∃! τ : H, IsFrobeniusElement H τ (Q.comap ι) q := hq_eq ▸ hexists_H_raw
  exact ⟨artinSymbol_tower G hexists_q hexists_qf,
    hexists_H,
    frobeniusElement_restriction G H ι ρ hcompat hexists_q hexists_H⟩
end FrobeniusTowerAndRestriction
section ArtinMapDef
variable {A : Type*} [CommRing A]
  (G : Type*) [CommGroup G]

/--
[artinMap_of](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean)
-/
@[path]
lemma artinMap_of
  [CommRing A]
  {S : Set (Ideal A)}
-- given
  (artinSymbolPrime : {𝔭 : Ideal A // 𝔭.IsPrime ∧ 𝔭 ∉ S} → G)
  (𝔭 : {𝔭 : Ideal A // 𝔭.IsPrime ∧ 𝔭 ∉ S}) :
-- imply
  artinMap G artinSymbolPrime (FreeAbelianGroup.of 𝔭) = Additive.ofMul (artinSymbolPrime 𝔭) := by
-- proof
  simp [artinMap, FreeAbelianGroup.lift_apply_of]
end ArtinMapDef


-- created on 2026-10-23
