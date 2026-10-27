import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.FiniteFields.Part5
open Polynomial in
open Polynomial IntermediateField


variable (p : ℕ) [Fact p.Prime] (n : ℕ)
/--
[𝔽q_isSplittingField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
`𝔽_p`, matching the splitting-field description in Definition 3.4. -/
lemma 𝔽q_isSplittingField :
  IsSplittingField (ZMod p) (𝔽q p n) (X ^ p ^ n - X : (ZMod p)[X]) := by
  show IsSplittingField (ZMod p) (SplittingField (X ^ p ^ n - X : (ZMod p)[X])) _
  infer_instance

variable (p : ℕ) [Fact p.Prime] (n : ℕ)
/--
[𝔽q_frobenius](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
i.e. `𝔽q p n` consists of roots of `X^(p^n) - X`. -/
lemma 𝔽q_frobenius (hn : n ≠ 0) (x : 𝔽q p n) : x ^ (p ^ n) = x := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  have hcard : Nat.card (𝔽q p n) = p ^ n := GaloisField.card p n hn
  rw [show p ^ n = Fintype.card (𝔽q p n) from by rw [Fintype.card_eq_nat_card]; omega]
  exact FiniteField.pow_card x

variable (p : ℕ) [Fact p.Prime] (n : ℕ)
/--
[𝔽q_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma 𝔽q_card (hn : n ≠ 0) : Nat.card (𝔽q p n) = p ^ n :=
  GaloisField.card p n hn

variable (p : ℕ) [Fact p.Prime] (n : ℕ)
/--
[𝔽q_card_thm36](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma 𝔽q_card_thm36 (hn : n ≠ 0) : Nat.card (𝔽q p n) = p ^ n :=
  GaloisField.card p n hn

variable (p : ℕ) [Fact p.Prime] (n : ℕ)
/--
[𝔽q_unique_of_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
cardinality `p^n` is isomorphic to `𝔽q p n`. -/
lemma 𝔽q_unique_of_card (hn : n ≠ 0)
  (K : Type*) [Field K] [Fintype K] (hK : Fintype.card K = p ^ n) :
  Nonempty (K ≃+* 𝔽q p n) :=
  ⟨𝔽q_ringEquiv_of_card p n hn K hK⟩

/--
[Fq_unique_of_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma Fq_unique_of_card
  {p : ℕ}
  [Fact p.Prime]
  {n : ℕ}
  [Field K]
  [Fintype K]
-- given
  (hn : n ≠ 0)
  (hcard : Fintype.card K = p ^ n) :
-- imply
  Nonempty (K ≃+* 𝔽q p n) :=
-- proof
  𝔽q_unique_of_card p n hn K hcard

/--
[finite_fields_isomorphic_of_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma finite_fields_isomorphic_of_card_eq
  {p : ℕ}
  [Fact p.Prime]
  {n : ℕ}
  {K₁ K₂ : Type*}
  [Field K₁]
  [Field K₂]
  [Fintype K₁]
  [Fintype K₂]
-- given
  (h : Fintype.card K₁ = Fintype.card K₂) :
-- imply
  Nonempty (K₁ ≃+* K₂) :=
-- proof
  ⟨FiniteField.ringEquivOfCardEq h⟩
section Theorem_3_8
variable (p : ℕ) [Fact p.Prime] (m n : ℕ)

variable (p : ℕ) [Fact p.Prime] (m n : ℕ)
/--
[𝔽q_subfield_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
`m ∣ n`. -/
lemma 𝔽q_subfield_iff (hm : m ≠ 0) (hn : n ≠ 0) :
  Nonempty (𝔽q p m →ₐ[ZMod p] 𝔽q p n) ↔ m ∣ n := by
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd,
    GaloisField.finrank p hm, GaloisField.finrank p hn]
end Theorem_3_8
section Theorem_3_3

/--
[Fp_canonical_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma Fp_canonical_map
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {K : Type*}
  [Field K]
  [CharP K p] :
-- imply
  ∃ f : 𝔽 p →+* K, Function.Injective f :=
-- proof
  ⟨ZMod.castHom (dvd_refl p) K, ZMod.castHom_injective K⟩

/--
[Fp_unique_of_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma Fp_unique_of_card
  {p : ℕ}
  {K : Type*}
  [Field K]
  [Fintype K]
-- given
  (hp : Nat.Prime p)
  (hK : Fintype.card K = p) :
-- imply
  Nonempty (𝔽 p ≃+* K) :=
-- proof
  ⟨ZMod.ringEquivOfPrime K hp hK⟩

/--
[fields_of_card_prime_isomorphic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma fields_of_card_prime_isomorphic
  {p : ℕ}
  {K₁ K₂ : Type*}
  [Field K₁]
  [Field K₂]
  [Fintype K₁]
  [Fintype K₂]
-- given
  (hp : Nat.Prime p)
  (hK₁ : Fintype.card K₁ = p)
  (hK₂ : Fintype.card K₂ = p) :
-- imply
  Nonempty (K₁ ≃+* K₂) := by
-- proof
  have e₁ := ZMod.ringEquivOfPrime K₁ hp hK₁
  have e₂ := ZMod.ringEquivOfPrime K₂ hp hK₂
  exact ⟨e₁.symm.trans e₂⟩

/--
[char_p_contains_Fp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma char_p_contains_Fp
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {K : Type*}
  [Field K]
  [CharP K p] :
-- imply
  ∃ f : 𝔽 p →+* K, Function.Injective f :=
-- proof
  Fp_canonical_map p K

/--
[Fp_unique_of_card_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma Fp_unique_of_card_prime
  {p : ℕ}
  {K : Type*}
  [Field K]
  [Fintype K]
-- given
  (hp : Nat.Prime p)
  (hK : Fintype.card K = p) :
-- imply
  Nonempty (𝔽 p ≃+* K) :=
-- proof
  Fp_unique_of_card p hp K hK
end Theorem_3_3
namespace Polynomial
section Def317
variable {k : Type*} [Field k]

namespace Polynomial

/--
[isSeparablePoly_iff_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma isSeparablePoly_iff_separable
  [Field k]
  {f : k[X]} :
-- imply
  IsSeparablePoly f ↔ f.Separable :=
-- proof
  Iff.rfl

end Polynomial

namespace Polynomial

/--
[isInseparablePoly_iff_not_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma isInseparablePoly_iff_not_separable
  [Field k]
  {f : k[X]} :
-- imply
  IsInseparablePoly f ↔ ¬f.Separable :=
-- proof
  Iff.rfl

end Polynomial

namespace Polynomial

/--
[separable_iff_coprime_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma separable_iff_coprime_derivative
  [Field k]
  {f : k[X]} :
-- imply
  f.Separable ↔ IsCoprime f (derivative f) :=
-- proof
  Iff.rfl

end Polynomial

namespace Polynomial

/--
[separable_iff_card_rootSet_eq_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma separable_iff_card_rootSet_eq_natDegree
  [Field k]
  [Field K]
  [Algebra k K]
  {f : k[X]}
-- given
  (hf : f ≠ 0)
  (hsplit : (f.map (algebraMap k K)).Splits) :
-- imply
  f.Separable ↔ Fintype.card (f.rootSet K) = f.natDegree :=
-- proof
  (card_rootSet_eq_natDegree_iff_of_splits hf hsplit).symm

end Polynomial

namespace Polynomial

/--
[separable_implies_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma separable_implies_squarefree
  [Field k]
  {f : k[X]}
-- given
  (hsep : f.Separable) :
-- imply
  Squarefree f :=
-- proof
  hsep.squarefree

end Polynomial

namespace Polynomial

/--
[separable_iff_squarefree_of_perfectField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma separable_iff_squarefree_of_perfectField
  [Field k]
  [PerfectField k]
  {f : k[X]} :
-- imply
  f.Separable ↔ Squarefree f :=
-- proof
  PerfectField.separable_iff_squarefree
end Def317
section Lem320

end Polynomial

namespace Polynomial

/--
[irreducible_inseparable_iff_derivative_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma irreducible_inseparable_iff_derivative_eq_zero
  [Field k]
  {f : k[X]}
-- given
  (hf : Irreducible f) :
-- imply
  ¬ f.Separable ↔ derivative f = 0 := by
-- proof
  rw [separable_iff_derivative_ne_zero hf, not_not]
end Polynomial
section Theorem_3_12


/--
[Polynomial.IsPrimitivePolynomial.monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma Polynomial.IsPrimitivePolynomial.monic
  {p : ℕ}
  [Fact p.Prime]
  {f : (ZMod p)[X]}
-- given
  (hf : f.IsPrimitivePolynomial p) :
-- imply
  f.Monic :=
-- proof
  hf.1

/--
[Polynomial.IsPrimitivePolynomial.irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma Polynomial.IsPrimitivePolynomial.irreducible
  {p : ℕ}
  [Fact p.Prime]
  {f : (ZMod p)[X]}
-- given
  (hf : f.IsPrimitivePolynomial p) :
-- imply
  Irreducible f :=
-- proof
  hf.2.1

/--
[Polynomial.IsPrimitivePolynomial.root_orderOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma Polynomial.IsPrimitivePolynomial.root_orderOf
  {p : ℕ}
  [Fact p.Prime]
  {f : (ZMod p)[X]}
-- given
  (hf : f.IsPrimitivePolynomial p) :
-- imply
  orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 :=
-- proof
  hf.2.2

/--
[perfectField_iff_irreducible_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma perfectField_iff_irreducible_separable
  {k : Type*}
  [Field k] :
-- imply
  PerfectField k ↔ ∀ f : k[X], Irreducible f → f.Separable := by
-- proof
  constructor
  · intro h f hf
    exact @PerfectField.separable_of_irreducible k _ h f hf
  · intro h
    exact ⟨fun hf => h _ hf⟩

/--
[finite_field_isPerfect](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma finite_field_isPerfect
  {K : Type*}
  [Field K]
  [Finite K] :
-- imply
  PerfectField K :=
-- proof
  inferInstance
section Theorem_3_9
variable (p : ℕ) [hp : Fact p.Prime]
open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]
/--
[quotient_irred_iso_𝔽q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
`𝔽_p[x]/(f) ≃ 𝔽_{p^{deg f}}`. -/
lemma quotient_irred_iso_𝔽q
  (f : (ZMod p)[X]) [hf : Fact (Irreducible f)] (hn : f.natDegree ≠ 0) :
  Nonempty (AdjoinRoot f ≃+* 𝔽q p f.natDegree) :=
  ⟨quotient_irred_ringEquiv_𝔽q p f hn⟩
end Theorem_3_9
section Corollary_3_10
variable (p : ℕ) [hp : Fact p.Prime]
open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]
/--
[irred_splits_in_𝔽q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
splits completely in `𝔽_{p^n}`. -/
lemma irred_splits_in_𝔽q
  (f : (ZMod p)[X]) (hf : Irreducible f) (hn : f.natDegree ≠ 0) :
  (f.map (algebraMap (ZMod p) (𝔽q p f.natDegree))).Splits := by
  haveI : Fact (Irreducible f) := ⟨hf⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  have hfr : Module.finrank (ZMod p) (AdjoinRoot f) = f.natDegree :=
    (AdjoinRoot.powerBasis hf0).finrank.trans (AdjoinRoot.powerBasis_dim hf0)
  have hgfr : Module.finrank (ZMod p) (𝔽q p f.natDegree) = f.natDegree :=
    GaloisField.finrank p hn
  have hdvd : Module.finrank (ZMod p) (AdjoinRoot f) ∣
    Module.finrank (ZMod p) (𝔽q p f.natDegree) := by
    rw [hfr, hgfr]
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
  let α := φ (AdjoinRoot.root f)
  have hα : aeval α f = 0 := by
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hint : IsIntegral (ZMod p) α := IsIntegral.of_finite (ZMod p) α
  have hmin_irr : Irreducible (minpoly (ZMod p) α) := minpoly.irreducible hint
  have hmin_dvd : minpoly (ZMod p) α ∣ f := minpoly.dvd _ _ hα
  have hf_dvd_min : f ∣ minpoly (ZMod p) α :=
    (hmin_irr.associated_of_dvd hf hmin_dvd).symm.dvd
  exact (Normal.splits' α).of_dvd
    (map_ne_zero (minpoly.ne_zero hint))
    (map_dvd _ hf_dvd_min)

/--
[Fq_irred_splits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma Fq_irred_splits
  {p : ℕ}
  [hp : Fact p.Prime]
  {f : (ZMod p)[X]}
-- given
  (hf : Irreducible f)
  (hn : f.natDegree ≠ 0) :
-- imply
  (f.map (algebraMap (ZMod p) (GaloisField p f.natDegree))).Splits :=
-- proof
  irred_splits_in_𝔽q p f hf hn
end Corollary_3_10
section Definition_3_16
variable (p : ℕ) [Fact p.Prime]
open Polynomial

/--
[primitive_poly_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma primitive_poly_exists
  {p : ℕ}
  [hp : Fact p.Prime]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∃ f : (ZMod p)[X], f.IsPrimitivePolynomial p ∧ f.natDegree = n := by
-- proof
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : IsCyclic (GaloisField p n)ˣ := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p n)ˣ)
  set α := (g : GaloisField p n) with hα
  have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
  set f := minpoly (ZMod p) α with hf_def
  have hf_monic : f.Monic := minpoly.monic hint
  have hf_irred : Irreducible f := minpoly.irreducible hint
  have htop : (ZMod p)⟮α⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    by_cases hx : x = 0
    · rw [hx]; exact (ZMod p)⟮α⟯.zero_mem
    · obtain ⟨m, hm⟩ := hg (Units.mk0 x hx)
      have : x = α ^ m := by
        have h := congr_arg Units.val hm.symm
        simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h
        exact h
      rw [this]
      exact zpow_mem (mem_adjoin_simple_self (ZMod p) (E := GaloisField p n) α) m
  have hf_deg : f.natDegree = n := by
    have h1 := adjoin.finrank hint
    have h2 : Module.finrank (ZMod p) ↥(ZMod p)⟮α⟯ =
      Module.finrank (ZMod p) (GaloisField p n) := by
      rw [htop]
      exact (IntermediateField.topEquiv (F := ZMod p)
        (E := GaloisField p n)).toLinearEquiv.finrank_eq
    rw [GaloisField.finrank p hn.ne'] at h2
    linarith
  have hf_order : orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 := by
    rw [hf_deg, orderOf_adjoinRoot_root_eq_orderOf (ZMod p) (GaloisField p n) α hint]
    have hord : orderOf α = orderOf g := by
      change orderOf ((Units.coeHom (GaloisField p n)) g) = orderOf g
      exact orderOf_injective (Units.coeHom _) Units.val_injective g
    rw [hord, orderOf_eq_card_of_forall_mem_zpowers hg]
    rw [Nat.card_units, GaloisField.card p n hn.ne']
  exact ⟨f, ⟨hf_monic, hf_irred, hf_order⟩, hf_deg⟩

/--
[nat_card_eq_mul_of_const_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma nat_card_eq_mul_of_const_fiber
  [Finite A]
  [Finite B]
  {f : A → B}
  {k : ℕ}
-- given
  (hfib : ∀ b : B, Nat.card {a : A // f a = b} = k) :
-- imply
  Nat.card A = k * Nat.card B := by
-- proof
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype B := Fintype.ofFinite B
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  simp_rw [hfib]; simp [Finset.sum_const, smul_eq_mul, mul_comm]

/--
[card_generators_eq_totient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma card_generators_eq_totient
  {p : ℕ}
  [hp : Fact p.Prime]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  Nat.card {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} = Nat.totient (p ^ n - 1) := by
-- proof
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p n) := Classical.decEq _
  have hcu : Fintype.card (GaloisField p n)ˣ = p ^ n - 1 := by
    rw [Fintype.card_eq_nat_card, Nat.card_units, GaloisField.card p n hn.ne']
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    IsCyclic.card_orderOf_eq_totient (by rw [hcu])]

/--
[minpoly_fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma minpoly_fiber_card
  {p : ℕ}
  [Fact p.Prime]
  {n : ℕ}
-- given
  (hn : 0 < n)
  (f : {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n}) :
-- imply
  Nat.card {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} // minpoly_of_generator p n hn g = f} = n := by
-- proof
  classical
  obtain ⟨hm, hirr, hord_root⟩ := f.2.1
  have hdeg := f.2.2
  have hfne : f.val ≠ 0 := hm.ne_zero
  haveI : Fact (Irreducible f.val) := ⟨hirr⟩
  haveI : Module.Finite (ZMod p) (AdjoinRoot f.val) := (AdjoinRoot.powerBasis hfne).finite
  haveI : Finite (AdjoinRoot f.val) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot f.val) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod p) (AdjoinRoot f.val) = n := by
    rw [(AdjoinRoot.powerBasis hfne).finrank, AdjoinRoot.powerBasis_dim]; exact hdeg
  have hcard : Fintype.card (AdjoinRoot f.val) = p ^ n := by
    rw [← FiniteField.pow_finrank_eq_card p (AdjoinRoot f.val), hfr]
  let e := GaloisField.algEquivGaloisFieldOfFintype p n hcard
  let α₀ : GaloisField p n := e (AdjoinRoot.root f.val)
  have hα₀_root : Polynomial.aeval α₀ f.val = 0 := by
    simp [α₀, aeval_algHom_apply]
  have hint : IsIntegral (ZMod p) α₀ := Algebra.IsIntegral.isIntegral α₀
  have hminpoly : minpoly (ZMod p) α₀ = f.val :=
    (minpoly.eq_of_irreducible_of_monic hirr hα₀_root hm).symm
  have hα₀_ord : orderOf α₀ = p ^ n - 1 := by
    show orderOf (e (AdjoinRoot.root f.val)) = p ^ n - 1
    have h_eq : orderOf (e (AdjoinRoot.root f.val)) = orderOf (AdjoinRoot.root f.val) :=
      MulEquiv.orderOf_eq e.toMulEquiv (AdjoinRoot.root f.val)
    rw [h_eq]; rwa [hdeg] at hord_root
  have hpn_pos : 0 < p ^ n - 1 := by
    have := Fact.out (self := ‹Fact p.Prime›); have : 1 < p ^ n := Nat.one_lt_pow hn.ne' this.one_lt
    omega
  have hα₀_ne : α₀ ≠ 0 := by intro h; rw [h, orderOf_zero] at hα₀_ord; omega
  let g₀ : (GaloisField p n)ˣ := Units.mk0 α₀ hα₀_ne
  have hg₀_val : (g₀ : GaloisField p n) = α₀ := rfl
  have hg₀_ord : orderOf g₀ = p ^ n - 1 := by
    rw [show orderOf g₀ = orderOf (g₀ : GaloisField p n) from
      (orderOf_injective (Units.coeHom _) Units.val_injective g₀).symm, hg₀_val, hα₀_ord]
  have htop : (ZMod p)⟮α₀⟯ = ⊤ := adjoin_top_of_unit_generator p n hn g₀ hg₀_ord
  let g₀_sub : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} := ⟨g₀, hg₀_ord⟩
  have hg₀_fib : minpoly_of_generator p n hn g₀_sub = f := Subtype.ext hminpoly
  have hGal_card : Nat.card (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) = n := by
    rw [IsGalois.card_aut_eq_finrank]; exact GaloisField.finrank p hn.ne'
  have alg_inj : ∀ σ τ : GaloisField p n ≃ₐ[ZMod p] GaloisField p n,
    σ α₀ = τ α₀ → σ = τ := by
    intro σ τ h
    have hsubalg : Algebra.adjoin (ZMod p) ({α₀} : Set (GaloisField p n)) = ⊤ := by
      rwa [← adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.isAlgebraic hint), htop]
    ext y; exact DFunLike.congr_fun
      (AlgHom.ext_of_adjoin_eq_top hsubalg (φ₁ := σ.toAlgHom) (φ₂ := τ.toAlgHom)
        (fun z hz => by simp only [Set.mem_singleton_iff] at hz; subst hz; exact h)) y
  let fwd : (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) →
    {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
      minpoly_of_generator p n hn g = f} := fun σ =>
    ⟨⟨Units.mk0 (σ α₀) (by intro h; exact hα₀_ne (σ.injective (by rwa [map_zero]))),
      by rw [show orderOf (Units.mk0 (σ α₀) _) = orderOf (σ α₀) from
        (orderOf_injective (Units.coeHom _) Units.val_injective _).symm]
        exact (MulEquiv.orderOf_eq σ.toMulEquiv α₀).trans hα₀_ord⟩,
      Subtype.ext (show minpoly (ZMod p) (σ α₀) = f.val from by
        rw [show minpoly (ZMod p) (σ α₀) = minpoly (ZMod p) α₀ from by
          rw [Normal.minpoly_eq_iff_mem_orbit (GaloisField p n)]; exact ⟨σ, rfl⟩]
        exact hminpoly)⟩
  have hfwd_inj : Function.Injective fwd := by
    intro σ τ h
    have heq : (σ α₀ : GaloisField p n) = (τ α₀ : GaloisField p n) := by
      have := congr_arg (fun g => (g.val.val : GaloisField p n)) h
      exact this
    exact alg_inj σ τ heq
  let bwd : {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
    minpoly_of_generator p n hn g = f} →
    (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) := fun g => by
    have hg_minpoly : minpoly (ZMod p) (g.val.val : GaloisField p n) = f.val :=
      congr_arg Subtype.val g.2
    have hg_orbit : (g.val.val : GaloisField p n) ∈
      MulAction.orbit (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) α₀ := by
      rw [← Normal.minpoly_eq_iff_mem_orbit (GaloisField p n)]
      rw [hg_minpoly, hminpoly]
    exact hg_orbit.choose
  have hbwd_spec : ∀ g, bwd g • α₀ = (g.val.val : GaloisField p n) := by
    intro g
    exact (by
      have hg_minpoly : minpoly (ZMod p) (g.val.val : GaloisField p n) = f.val :=
        congr_arg Subtype.val g.2
      have hg_orbit : (g.val.val : GaloisField p n) ∈
        MulAction.orbit (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) α₀ := by
        rw [← Normal.minpoly_eq_iff_mem_orbit (GaloisField p n)]
        rw [hg_minpoly, hminpoly]
      exact hg_orbit.choose_spec)
  have hbwd_inj : Function.Injective bwd := by
    intro g₁ g₂ h
    have h1 := hbwd_spec g₁
    have h2 := hbwd_spec g₂
    rw [h] at h1
    have : (g₁.val.val : GaloisField p n) = (g₂.val.val : GaloisField p n) := by
      rw [← h1, ← h2]
    have h_val1 : g₁.val.val = g₂.val.val := Units.ext this
    exact Subtype.ext (Subtype.ext h_val1)
  haveI : Finite (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) := by
    exact Nat.finite_of_card_ne_zero (by rw [hGal_card]; omega)
  haveI : Finite {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
    minpoly_of_generator p n hn g = f} := by
    exact Finite.of_injective bwd hbwd_inj
  have h_le : Nat.card {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
    minpoly_of_generator p n hn g = f} ≤ n := by
    calc Nat.card _ ≤ Nat.card (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) :=
      Nat.card_le_card_of_injective bwd hbwd_inj
      _ = n := hGal_card
  have h_ge : n ≤ Nat.card {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
    minpoly_of_generator p n hn g = f} := by
    calc n = Nat.card (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) := hGal_card.symm
      _ ≤ Nat.card _ := Nat.card_le_card_of_injective fwd hfwd_inj
  omega

/--
[primitive_poly_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
lemma primitive_poly_count
  {p : ℕ}
  [Fact p.Prime]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  Nat.card {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n} = Nat.totient (p ^ n - 1) / n := by
-- proof
  have hmul := nat_card_eq_mul_of_const_fiber (minpoly_of_generator p n hn) n
    (minpoly_fiber_card p n hn)
  rw [card_generators_eq_totient p n hn] at hmul
  rw [Nat.eq_div_iff_mul_eq_left (by omega) ⟨_, hmul⟩]
  linarith

/--
[finite_mult_subgroup_of_field_isCyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
private lemma finite_mult_subgroup_of_field_isCyclic_eq
  {k : Type*}
  [Field k]
  {G : Subgroup kˣ}
  [Finite G] :
-- imply
  IsCyclic G := by
-- proof
  apply finite_mult_subgroup_of_field_isCyclic k G

/--
[finite_field_mult_isCyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
private lemma finite_field_mult_isCyclic_eq
  {k : Type*}
  [Field k]
  [Fintype k] :
-- imply
  IsCyclic kˣ := by
-- proof
  apply finite_field_mult_isCyclic k

/--
[quotient_irred_iso_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
private lemma quotient_irred_iso__eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {f : (ZMod p)[X]}
  [hf : Fact (Irreducible f)]
-- given
  (hn : f.natDegree ≠ 0) :
-- imply
  Nonempty (AdjoinRoot f ≃+* 𝔽q p f.natDegree) := by
-- proof
  apply quotient_irred_iso_ p f hn

/--
[irred_splits_in_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
private lemma irred_splits_in__eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {f : (ZMod p)[X]}
-- given
  (hf : Irreducible f)
  (hn : f.natDegree ≠ 0) :
-- imply
  (f.map (algebraMap (ZMod p) (𝔽q p f.natDegree))).Splits := by
-- proof
  apply irred_splits_in_ p f hf hn

/--
[orderOf_adjoinRoot_root_eq_orderOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
private lemma orderOf_adjoinRoot_root_eq_orderOf_eq
  {F : Type*}
  [Field F]
  {E : Type*}
  [Field E]
  [Algebra F E]
  {α : E}
-- given
  (hint : IsIntegral F α) :
-- imply
  orderOf (AdjoinRoot.root (minpoly F α)) = orderOf α := by
-- proof
  apply orderOf_adjoinRoot_root_eq_orderOf F E α hint

/--
[adjoin_top_of_unit_generator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
private lemma adjoin_top_of_unit_generator_eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {n : ℕ}
  {g : (GaloisField p n)ˣ}
-- given
  (hn : 0 < n)
  (hg : orderOf g = p ^ n - 1) :
-- imply
  (ZMod p)⟮(g : GaloisField p n)⟯ = ⊤ := by
-- proof
  apply adjoin_top_of_unit_generator p n hn g hg

/--
[generator_minpoly_is_prim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean)
-/
@[path]
private lemma generator_minpoly_is_prim_eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {n : ℕ}
  {g : (GaloisField p n)ˣ}
-- given
  (hn : 0 < n)
  (hg : orderOf g = p ^ n - 1) :
-- imply
  let f := minpoly (ZMod p) (g : GaloisField p n) f.IsPrimitivePolynomial p ∧ f.natDegree = n := by
-- proof
  apply generator_minpoly_is_prim p n hn g hg


-- created on 2026-10-23
