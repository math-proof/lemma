/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean -/

import sympy.atlas.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-- The canonical primitive `n`-th root of unity `ζₙ = exp (2 * π * I / n)`. -/
private noncomputable def zeta (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- The quadratic `X² - sX + 1` over `ℚ⟮s⟯`, where `s = ζ + ζ⁻¹`. -/
private noncomputable def quadPoly (n : ℕ) :
    Polynomial (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)) :=
  Polynomial.X ^ 2 + (-(Polynomial.C ⟨zeta n + (zeta n)⁻¹,
        IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩ * Polynomial.X) + 1)

/-- `ℚ⟮s⟯`, the base field for the quadratic step, where `s = ζ + ζ⁻¹`. -/
private noncomputable abbrev baseField (n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)

/-- `ℚ⟮s⟯ ≤ ℚ⟮ζ⟯`. -/
private lemma baseField_le (n : ℕ) :
    baseField n ≤ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  rw [hx]
  apply add_mem
  · exact IntermediateField.mem_adjoin_simple_self ℚ (zeta n)
  · exact inv_mem (IntermediateField.mem_adjoin_simple_self ℚ (zeta n))

/-- Tower algebra `ℚ⟮s⟯ → ℚ⟮ζ⟯` from the inclusion. -/
private noncomputable instance towerAlgebra (n : ℕ) : Algebra ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
  (IntermediateField.inclusion (baseField_le n)).toRingHom.toAlgebra

/-- Tower property for `ℚ → ℚ⟮s⟯ → ℚ⟮ζ⟯`. -/
private noncomputable instance towerIsScalarTower (n : ℕ) : IsScalarTower ℚ ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    have hcomm := (IntermediateField.inclusion (baseField_le n)).commutes x
    have hdef : ∀ y : ↥(baseField n),
        algebraMap ↥(baseField n)
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) y
        = IntermediateField.inclusion (baseField_le n) y := fun y => rfl
    rw [hdef]
    exact hcomm)

/-- The tower algebra acts by inclusion. -/
private lemma towerAlgebra_apply (n : ℕ) (c : ↥(baseField n)) :
    algebraMap ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) c
    = IntermediateField.inclusion (baseField_le n) c := rfl

/-- Coercion of the tower inclusion is the field coercion. -/
private lemma towerCoe (n : ℕ) (c : ↥(baseField n)) :
    ((algebraMap ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) c
      : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
    = algebraMap ↥(baseField n) ℂ c := by
  rw [towerAlgebra_apply, IntermediateField.coe_inclusion]
  simp only [IntermediateField.algebraMap_apply]

/-- `finrank ℚ⟮s⟯ ℚ⟮ζ⟯ = 2`. -/
private lemma finrank_baseField (n : ℕ) (hn : 2 < n) :
    Module.finrank ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) = 2 := by
  have hQint : IsIntegral ℚ (zeta n) :=
    (zeta_isIntegral n (by omega)).tower_top
  have hKint : IsIntegral ↥(baseField n) (zeta n) := hQint.tower_top
  have hmemE : zeta n ∈ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) :=
    IntermediateField.mem_adjoin_simple_self ℚ (zeta n)
  have hfinQ : Module.Finite ℚ ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
    IntermediateField.adjoin.finiteDimensional hQint
  have hfin : Module.Finite ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
    Module.Finite.right ℚ ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))
  have h2le : 2 ≤ Module.finrank ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) := by
    have hindep : LinearIndependent ↥(baseField n)
        ![1, (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        simp only [zero_smul, add_zero] at hst
        have hs0 : s = 0 := by
          apply Subtype.val_injective
          have h2 := congrArg Subtype.val hst
          rw [Algebra.smul_def, coeE_mul, coeE_one, mul_one, towerCoe] at h2
          rw [coeE_zero] at h2
          exact h2
        exact ⟨hs0, rfl⟩
      · exfalso
        have e1 : t • (⟨zeta n, hmemE⟩ :
            ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))
            = -(s • (1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))) :=
          eq_neg_of_add_eq_zero_right hst
        have e2 : t • algebraMap ↥(baseField n)
            ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) (-(t⁻¹ * s))
            = -(s • (1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))) := by
          rw [Algebra.smul_def, ← map_mul]
          have hfield : t * (-(t⁻¹ * s)) = -s := by
            field_simp
          rw [hfield, map_neg, Algebra.smul_def, mul_one]
        have halg : algebraMap ↥(baseField n)
            ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) (-(t⁻¹ * s))
            = (⟨zeta n, hmemE⟩ :
              ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) :=
          smul_right_injective _ ht (by
            change t • algebraMap ↥(baseField n)
              ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) (-(t⁻¹ * s))
              = t • (⟨zeta n, hmemE⟩ :
                ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))
            rw [e2, e1])
        have hζc : (((-(t⁻¹ * s) : ↥(baseField n))) : ℂ) = zeta n := by
          have h2 := congrArg Subtype.val halg
          rw [towerCoe, coeE_zeta] at h2
          exact h2
        have hmem : zeta n ∈ baseField n := by
          rw [← hζc]
          exact (-(t⁻¹ * s)).property
        exact zeta_not_mem_adjoin n hn hmem
    have hcard := LinearIndependent.fintype_card_le_finrank hindep
    rwa [Fintype.card_fin 2] at hcard
  have hspan : Submodule.span ↥(baseField n)
      (Set.range ![1, (⟨zeta n, hmemE⟩ :
        ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))]) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨a, b, hab⟩ := mem_affine n (y : ℂ) y.property
    have hcomb : a • (1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))
        + b • (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) = y := by
      apply Subtype.ext
      rw [Algebra.smul_def, Algebra.smul_def]
      have push : ∀ u v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)),
          ((u + v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
          = (u : ℂ) + (v : ℂ) := fun u v => rfl
      have pushm : ∀ u v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)),
          ((u * v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
          = (u : ℂ) * (v : ℂ) := fun u v => rfl
      have pusho : ((1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
          = 1 := rfl
      have pushz : (((⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))) : ℂ) = zeta n := rfl
      rw [push, pushm, pushm, pusho, pushz, towerCoe n a, towerCoe n b, mul_one]
      exact hab
    have hmem : y ∈ Submodule.span ↥(baseField n)
        ({1, (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))} : Set _) := by
      rw [Submodule.mem_span_pair]
      exact ⟨a, b, hcomb⟩
    have hset : ({1, (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))} : Set _)
        = Set.range ![1, (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))] := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
      · rintro ⟨i, hi⟩
        fin_cases i
        · simp at hi
          exact Or.inl hi.symm
        · simp at hi
          exact Or.inr hi.symm
    rw [← hset]
    exact hmem
  have hle2 : Module.finrank ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) ≤ 2 := by
    have h := finrank_le_of_span_eq_top hspan
    calc Module.finrank ↥(baseField n)
            ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))
        ≤ Fintype.card (Fin 2) := h
      _ = 2 := Fintype.card_fin 2
  have hpos : 0 < Module.finrank ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) := Module.finrank_pos
  omega

/-- Tower equation: `deg ℚ s * 2 = φ(n)`. -/
private lemma tower_degree_eq (n : ℕ) (hn : 2 < n) :
    (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree * 2 = n.totient := by
  have h := Module.finrank_mul_finrank ℚ ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))
  rwa [finrank_adjoin_trace n (by omega),
    finrank_baseField n hn, finrank_adjoin_zeta n (by omega)] at h

/-- The `ℤ`-minpoly degree of `s` is `φ(n)/2`. -/
private lemma natDegree_psi_eq (n : ℕ) (hn : 2 < n) :
    (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree = n.totient / 2 := by
  have htow := tower_degree_eq n hn
  obtain ⟨d, hd⟩ := Nat.totient_even hn
  have he : (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree = d := by omega
  rw [← natDegree_psi_rat n (by omega), he]
  omega

/-- For `2 < n`, `n.totient` is even and the `natDegree` of the real cyclotomic
polynomial `realCyclotomicPolynomial n` equals `n.totient / 2`. The `Even`
conjunct makes the source's exact half machine-visible under natural-number
division.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials
of Algebraic Cosine Values at Rational Multiples of π", Journal of Integer
Sequences 19 (2016), source lines 83–90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex

Proves `Wanted` entry `natDegree_realCyclotomicPolynomial`.
-/
theorem natDegree_realCyclotomicPolynomial (n : ℕ) (hn : 2 < n) :
    Even n.totient ∧ (realCyclotomicPolynomial n).natDegree = n.totient / 2 :=
  ⟨Nat.totient_even hn, natDegree_psi_eq n hn⟩

/-- The cleared polynomial `R(X) = Σₖ aₖ X^(e-k) (X²+1)^k`, where `ψ = Σₖ aₖ X^k`
is the real cyclotomic polynomial of degree `e`. -/
private noncomputable def clearPoly (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree + 1),
    Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (Polynomial.X ^ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree - k)
        * (Polynomial.X ^ 2 + 1) ^ k)

/-- `R = Φₙ`. -/
private lemma clearPoly_eq (n : ℕ) (hn : 2 < n) :
    clearPoly n = Polynomial.cyclotomic n ℤ := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  have hP : Polynomial.cyclotomic n ℤ = minpoly ℤ (zeta n) :=
    Polynomial.cyclotomic_eq_minpoly hζ (by omega)
  have hdvd : Polynomial.cyclotomic n ℤ ∣ clearPoly n := by
    rw [hP]
    apply minpoly.isIntegrallyClosed_dvd (zeta_isIntegral n (by omega))
    exact clearPoly_aeval n
  have hdegP : (Polynomial.cyclotomic n ℤ).natDegree = n.totient :=
    Polynomial.natDegree_cyclotomic n ℤ
  have he := natDegree_psi_eq n hn
  have hRdeg := clearPoly_natDegree n hn
  have hle : (clearPoly n).natDegree ≤ (Polynomial.cyclotomic n ℤ).natDegree := by
    rw [hRdeg, hdegP, he]
    obtain ⟨d, hd⟩ := Nat.totient_even hn
    omega
  have h := Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.cyclotomic.monic n ℤ) (clearPoly_monic n hn) hdvd hle
  exact h

/-- Laurent transfer: `toLaurent R = T^d · ψ(T + T⁻¹)`. -/
private lemma transfer (n : ℕ) (hn : 2 < n) :
    Polynomial.toLaurent (clearPoly n)
      = LaurentPolynomial.T (((n.totient / 2 : ℕ)) : ℤ)
        * Polynomial.aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
          (minpoly ℤ (zeta n + (zeta n)⁻¹)) := by
  have hTS : (LaurentPolynomial.T (2 : ℤ) + 1 : LaurentPolynomial ℤ)
      = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) := by
    have h2 : (LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ)
        = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          * (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) := by
      have h22 : (2 : ℤ) = 1 + 1 := by norm_num
      rw [h22, LaurentPolynomial.T_add]
    have h10 : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          * (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)
        = (1 : LaurentPolynomial ℤ) := by
      have h00 : (1 : ℤ) + (-1) = 0 := by norm_num
      have hT : (LaurentPolynomial.T ((1 : ℤ) + (-1)) : LaurentPolynomial ℤ)
          = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            * (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ) :=
        LaurentPolynomial.T_add (1 : ℤ) (-1)
      rw [h00, LaurentPolynomial.T_zero] at hT
      exact hT.symm
    rw [h2, ← h10, mul_add]
  have hT1k : ∀ k : ℕ, ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) ^ k
      = (LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ)) := by
    intro k
    rw [LaurentPolynomial.T_pow, mul_one]
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hed : e = n.totient / 2 := by
    rw [he]
    exact natDegree_psi_eq n hn
  have hcast : ∀ k : ℕ, k ≤ e →
      ((((e - k : ℕ))) : ℤ) + ((((k : ℕ))) : ℤ) = ((((e : ℕ))) : ℤ) := by
    intro k hke
    rw [← Nat.cast_add]
    congr 1
    omega
  have hterm : ∀ k : ℕ, k ≤ e →
      (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ) + 1) ^ k
      = (LaurentPolynomial.T ((((n.totient / 2 : ℕ))) : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
    intro k hke
    calc (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ) + 1) ^ k
        = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))) ^ k := by
          rw [hTS]
      _ = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * (((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)) ^ k
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k) := by
          rw [mul_pow]
      _ = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k) := by
          rw [hT1k k]
      _ = ((LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * (LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ))
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          ring
      _ = (LaurentPolynomial.T (((((e - k : ℕ))) : ℤ) + ((((k : ℕ))) : ℤ)) :
              LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [← LaurentPolynomial.T_add]
      _ = (LaurentPolynomial.T ((((e : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [hcast k hke]
      _ = (LaurentPolynomial.T ((((n.totient / 2 : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [hed]
  have haeval : Polynomial.aeval
      ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))
      (minpoly ℤ (zeta n + (zeta n)⁻¹))
      = ∑ k ∈ Finset.range (e + 1),
        LaurentPolynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
    have h := Polynomial.as_sum_range_C_mul_X_pow (minpoly ℤ (zeta n + (zeta n)⁻¹))
    have h2 := congrArg
      (Polynomial.aeval ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))) h
    simp only [map_sum, Polynomial.aeval_C, map_mul, map_pow, Polynomial.aeval_X,
      ← LaurentPolynomial.C_eq_algebraMap] at h2
    rw [← he] at h2
    rw [← h2]
  rw [map_sum, haeval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hke : k ≤ e := by
    have hmem := Finset.mem_range.mp hk
    omega
  simp only [map_mul, map_pow, map_add, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X]
  have h2' : ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) ^ 2
      = (LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ)) := by
    simpa only [Nat.cast_ofNat] using hT1k 2
  rw [hT1k (e - k), h2', hterm k hke]
  ring

/-- Denominator-cleared Laurent-polynomial form of `ψₙ(x + x⁻¹) = x^(-φ(n)/2) Φₙ(x)`:
multiplying the evaluation of the real cyclotomic polynomial at `x + x⁻¹` by
`x ^ (φ(n) / 2)` recovers the cyclotomic polynomial as a Laurent polynomial.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of
Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19
(2016), source lines 83-90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455
normalized no-final-newline span SHA-256
e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039

Proves `Wanted` entry `lehmer_cyclotomic_identity`.
-/
theorem lehmer_cyclotomic_identity (n : ℕ) (hn : 2 < n) :
    LaurentPolynomial.T (↑(n.totient / 2)) *
      Polynomial.aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
        (realCyclotomicPolynomial n) =
      Polynomial.toLaurent (Polynomial.cyclotomic n ℤ) := by
  have hR := clearPoly_eq n hn
  have htrans := transfer n hn
  have hdef : realCyclotomicPolynomial n
      = minpoly ℤ (zeta n + (zeta n)⁻¹) := rfl
  rw [hdef, ← hR]
  exact htrans.symm

end MetaMathlibExt
