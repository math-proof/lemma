import Mathlib
import Initialize.Tactic.Attr.Basic
open Ideal MvPolynomial Order


namespace FiniteMorphismDimension

/--
[PrimeSpectrum.comap_strictMono_of_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionResults.lean)
-/
@[path]
lemma PrimeSpectrum.comap_strictMono_of_isIntegral
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Algebra.IsIntegral B A] :
-- imply
  StrictMono (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  intro p q hpq
  have hpq' : p.asIdeal < q.asIdeal := hpq
  obtain ⟨hle, x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp hpq'
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxq, hxp⟩
    (Algebra.IsIntegral.isIntegral x)

end FiniteMorphismDimension

namespace FiniteMorphismDimension

/--
[ringKrullDim_le_of_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionResults.lean)
-/
@[path]
lemma ringKrullDim_le_of_integral
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Algebra.IsIntegral B A] :
-- imply
  ringKrullDim A ≤ ringKrullDim B :=
-- proof
  krullDim_le_of_strictMono _ PrimeSpectrum.comap_strictMono_of_isIntegral

end FiniteMorphismDimension

namespace FiniteMorphismDimension

/--
[exists_lift_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionResults.lean)
-/
@[path]
lemma exists_lift_chain
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Algebra.IsIntegral B A]
  {n : ℕ}
  {f : Fin (n + 1) → PrimeSpectrum B}
-- given
  (hinj : Function.Injective (algebraMap B A))
  (hf : ∀ i : Fin n, f i.castSucc < f i.succ) :
-- imply
  ∃ g : Fin (n + 1) → PrimeSpectrum A, (∀ i, PrimeSpectrum.comap (algebraMap B A) (g i) = f i) ∧ (∀ i : Fin n, g i.castSucc < g i.succ) := by
-- proof
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) :=
    RingHom.IsIntegral.comap_surjective (Algebra.isIntegral_def.mp inferInstance) hinj
  induction n with
  | zero =>
    obtain ⟨q, hq⟩ := hsurj (f 0)
    exact ⟨fun _ => q, fun i => by fin_cases i; exact hq, fun i => by fin_cases i⟩
  | succ n ih =>
    have hf' : ∀ i : Fin n, (f ∘ Fin.castSucc) i.castSucc < (f ∘ Fin.castSucc) i.succ :=
      fun i => hf i.castSucc
    obtain ⟨g', hg'_comap, hg'_strict⟩ := ih (f ∘ Fin.castSucc) hf'
    have hle : (g' (Fin.last n)).asIdeal.comap (algebraMap B A) ≤
      (f (Fin.last (n + 1))).asIdeal := by
      have h := congr_arg PrimeSpectrum.asIdeal (hg'_comap (Fin.last n))
      simp only [Function.comp, PrimeSpectrum.comap_asIdeal] at h
      rw [h]; exact le_of_lt (hf (Fin.last n))
    obtain ⟨Q, hQ_ge, hQ_prime, hQ_comap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral
        (f (Fin.last (n + 1))).asIdeal (g' (Fin.last n)).asIdeal hle
    let qLast : PrimeSpectrum A := ⟨Q, hQ_prime⟩
    refine ⟨Fin.snoc g' qLast, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact PrimeSpectrum.ext hQ_comap
      · intro j; simp only [Fin.snoc_castSucc]; exact hg'_comap j
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last]
        refine lt_of_le_of_ne hQ_ge ?_
        intro heq
        have h1 : PrimeSpectrum.comap (algebraMap B A) qLast = f (Fin.last (n + 1)) :=
          PrimeSpectrum.ext hQ_comap
        have h2 := hg'_comap (Fin.last n)
        simp only [Function.comp] at h2
        have h3 : f (Fin.last (n + 1)) = f (Fin.castSucc (Fin.last n)) := by
          rw [← h1, ← h2, heq]
        exact absurd h3.symm (ne_of_lt (hf (Fin.last n)))
      · intro j; simp only [Fin.snoc_castSucc, Fin.succ_castSucc]; exact hg'_strict j

end FiniteMorphismDimension

namespace FiniteMorphismDimension

/--
[ringKrullDim_ge_of_injective_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionResults.lean)
-/
@[path]
lemma ringKrullDim_ge_of_injective_integral
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Algebra.IsIntegral B A]
-- given
  (hinj : Function.Injective (algebraMap B A)) :
-- imply
  ringKrullDim B ≤ ringKrullDim A := by
-- proof
  unfold ringKrullDim
  apply iSup_le
  intro chain_B
  obtain ⟨g, _, hg_strict⟩ := exists_lift_chain hinj chain_B.length chain_B.toFun chain_B.step
  exact le_iSup_of_le ⟨chain_B.length, g, hg_strict⟩ le_rfl

end FiniteMorphismDimension

namespace FiniteMorphismDimension

/--
[ringKrullDim_eq_of_injective_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionResults.lean)
-/
@[path]
lemma ringKrullDim_eq_of_injective_finite
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
-- given
  (hinj : Function.Injective (algebraMap B A)) :
-- imply
  ringKrullDim A = ringKrullDim B := by
-- proof
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  exact le_antisymm ringKrullDim_le_of_integral (ringKrullDim_ge_of_injective_integral hinj)

end FiniteMorphismDimension

/--
[ringKrullDim_eq_of_finite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionResults.lean)
-/
@[path]
lemma ringKrullDim_eq_of_finite_injective
  [CommRing R]
  [CommRing S]
  {φ : R →+* S}
-- given
  (hfin : letI := φ.toAlgebra; Module.Finite R S)
  (hinj : Function.Injective φ) :
-- imply
  ringKrullDim S = ringKrullDim R := by
-- proof
  letI : Algebra R S := φ.toAlgebra
  have : Function.Injective (algebraMap R S) := hinj
  exact FiniteMorphismDimension.ringKrullDim_eq_of_injective_finite this

/--
[mvPolynomial_Fin_maximal_height_eq_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionResults.lean)
-/
@[path]
lemma mvPolynomial_Fin_maximal_height_eq_dim
  {k : Type*}
  [Field k]
  {n : ℕ}
  {m : Ideal (MvPolynomial (Fin n) k)}
  [m.IsMaximal] :
-- imply
  (m.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) k) := by
-- proof
  induction n with
  | zero =>
    let e := (isEmptyAlgEquiv k (Fin 0)).toRingEquiv
    have hm : (Ideal.map e m).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hbot : Ideal.map e m = ⊥ := by
      obtain h | h := (Ideal.map e m).eq_bot_or_top
      · exact h
      · exact absurd h hm.ne_top
    rw [← e.height_map m, hbot, Ideal.height_bot]
    simp [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field]
  | succ n ih =>
    let e := (finSuccEquiv k n).toRingEquiv
    let m' := Ideal.map e m
    have hm' : m'.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hcomap : (m'.comap Polynomial.C).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing m'
    have hlo : m'.LiesOver (m'.comap Polynomial.C) := ⟨rfl⟩
    have hih := ih (m'.comap Polynomial.C)
    rw [← e.height_map m, @Polynomial.height_eq_height_add_one _ _ _
      (m'.comap Polynomial.C) m' hm' hlo,
      WithBot.coe_add, WithBot.coe_one, hih,
      ringKrullDim_eq_of_ringEquiv e, Polynomial.ringKrullDim_of_isNoetherianRing]

/--
[ringKrullDim_mvPolynomial_quotient_non_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionResults.lean)
-/
@[path]
lemma ringKrullDim_mvPolynomial_quotient_non_constant
  {k : Type*}
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin n) k}
-- given
  (hn : n ≥ 1)
  (hf : f ∉ Set.range (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)) :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) = ↑(n - 1 : ℕ) := by
-- proof
  have hnu : ¬ IsUnit f := by
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
    push Not
    intro r _ h; exact hf ⟨r, h.symm⟩
  have hne : f ≠ 0 := by
    intro h; exact hf ⟨0, by rw [h, map_zero]⟩
  have hnzd : f ∈ nonZeroDivisors (MvPolynomial (Fin n) k) :=
    mem_nonZeroDivisors_of_ne_zero hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hnu)
  haveI : m.IsMaximal := hm
  have hht := mvPolynomial_Fin_maximal_height_eq_dim k n m
  have key := Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
    hnzd hht (hle (Ideal.mem_span_singleton_self f))
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, zero_add] at key
  have hfin : Nat.card (Fin n) = n := Nat.card_fin n
  rw [hfin] at key
  set d := ringKrullDim (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) with hd_def
  have hd_ne_bot : d ≠ ⊥ := by
    intro h; rw [h] at key; exact absurd key (by simp [WithBot.bot_add])
  obtain ⟨d', hd'⟩ := WithBot.ne_bot_iff_exists.mp hd_ne_bot
  rw [← hd'] at key ⊢
  rw [show (↑d' + 1 : WithBot ℕ∞) = ↑(d' + 1) from rfl] at key
  have h2 := WithBot.coe_injective key
  congr 1
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one, Nat.cast_succ] at h2 ⊢
  exact WithTop.add_right_cancel WithTop.one_ne_top h2


-- created on 2026-10-23
