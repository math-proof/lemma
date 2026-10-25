/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean -/

import Def.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
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
import Instance.NumberTheory.Cyclotomic.LehmerLaurentIdentity


namespace MetaMathlibExt

/-- The tower algebra acts by inclusion. -/
lemma towerAlgebra_apply (n : ℕ) (c : ↥(baseField n)) :
    algebraMap ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) c
    = IntermediateField.inclusion (baseField_le n) c := rfl

/-- Coercion of the tower inclusion is the field coercion. -/
lemma towerCoe (n : ℕ) (c : ↥(baseField n)) :
    ((algebraMap ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) c
      : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
    = algebraMap ↥(baseField n) ℂ c := by
  rw [towerAlgebra_apply, IntermediateField.coe_inclusion]
  simp only [IntermediateField.algebraMap_apply]

/-- `finrank ℚ⟮s⟯ ℚ⟮ζ⟯ = 2`. -/
lemma finrank_baseField (n : ℕ) (hn : 2 < n) :
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
lemma tower_degree_eq (n : ℕ) (hn : 2 < n) :
    (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree * 2 = n.totient := by
  have h := Module.finrank_mul_finrank ℚ ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))
  rwa [finrank_adjoin_trace n (by omega),
    finrank_baseField n hn, finrank_adjoin_zeta n (by omega)] at h

/-- The `ℤ`-minpoly degree of `s` is `φ(n)/2`. -/
lemma natDegree_psi_eq (n : ℕ) (hn : 2 < n) :
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

end MetaMathlibExt
