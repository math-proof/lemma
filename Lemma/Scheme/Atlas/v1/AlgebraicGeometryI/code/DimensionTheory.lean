import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.DimensionTheory
open Ideal


/--
[ringKrullDim_quotient_span_succ_le_of_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma ringKrullDim_quotient_span_succ_le_of_domain
  [CommRing A]
  [IsDomain A]
  {g : A}
-- given
  (hg : g ≠ 0) :
-- imply
  ringKrullDim (A ⧸ Ideal.span {g}) + 1 ≤ ringKrullDim A :=
-- proof
  ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg)

/--
[ringKrullDim_localization_away_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma ringKrullDim_localization_away_le
  [CommRing A]
  {f : A} :
-- imply
  ringKrullDim (Localization.Away f) ≤ ringKrullDim A := by
-- proof
  unfold ringKrullDim
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A (Localization.Away f)))
  intro a b hab
  exact lt_of_le_of_ne (Ideal.comap_mono hab.le) fun heq =>
    hab.ne (PrimeSpectrum.localization_comap_injective _ (Submonoid.powers f) heq)

/--
[height_preserved_by_localization_away](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma height_preserved_by_localization_away
  [CommRing A]
  [IsNoetherianRing A]
  {f : A}
  {P : Ideal A}
  [P.IsPrime]
-- given
  (hfP : Disjoint (Submonoid.powers f : Set A) (P : Set A)) :
-- imply
  (P.map (algebraMap A (Localization.Away f))).height = P.height :=
-- proof
  IsLocalization.height_map_of_disjoint (Submonoid.powers f) P hfP

/--
[minimalPrime_ne_bot_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma minimalPrime_ne_bot_of_nonzero
  [CommRing A]
  [IsDomain A]
  {g : A}
  {P : Ideal A}
-- given
  (hg : g ≠ 0)
  (hP : P ∈ (Ideal.span ({g} : Set A)).minimalPrimes) :
-- imply
  P ≠ ⊥ := by
-- proof
  haveI := Ideal.minimalPrimes_isPrime hP
  intro hbot
  have : g ∈ P := hP.1.2 (subset_span (Set.mem_singleton g))
  rw [hbot] at this
  exact hg (Ideal.mem_bot.mp this)

/--
[height_eq_one_of_minimalPrime_span_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma height_eq_one_of_minimalPrime_span_domain
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {g : A}
  {P : Ideal A}
  [P.IsPrime]
-- given
  (hg : g ≠ 0)
  (hP : P ∈ (Ideal.span ({g} : Set A)).minimalPrimes) :
-- imply
  P.height = 1 := by
-- proof
  have h_le : P.height ≤ 1 := by
    have : Submodule.IsPrincipal (Ideal.span ({g} : Set A)) := ⟨⟨g, by simp⟩⟩
    exact height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  have h_ne : P.height ≠ 0 := by
    rw [height_eq_primeHeight]
    intro h0
    have hmem : P ∈ minimalPrimes A := Ideal.primeHeight_eq_zero_iff.mp h0
    change P ∈ (⊥ : Ideal A).minimalPrimes at hmem
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at hmem
    have hPbot : P = ⊥ := Set.mem_singleton_iff.mp hmem
    exact minimalPrime_ne_bot_of_nonzero g hg P hP hPbot
  exact le_antisymm h_le (ENat.one_le_iff_ne_zero.mpr h_ne)

/--
[one_add_ringKrullDim_quotient_minimalPrime_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma one_add_ringKrullDim_quotient_minimalPrime_le
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {g : A}
  {P : Ideal A}
  [P.IsPrime]
-- given
  (hg : g ≠ 0)
  (hP : P ∈ (Ideal.span ({g} : Set A)).minimalPrimes) :
-- imply
  (1 : WithBot ℕ∞) + ringKrullDim (A ⧸ P) ≤ ringKrullDim A := by
-- proof
  have h_ht : P.height = 1 := height_eq_one_of_minimalPrime_span_domain g hg P hP
  calc (1 : WithBot ℕ∞) + ringKrullDim (A ⧸ P)
    = ↑P.height + ringKrullDim (A ⧸ P) := by rw [h_ht]; rfl
    _ ≤ ringKrullDim A := height_add_ringKrullDim_quotient_le P

/--
[ringKrullDim_quotient_minimalPrime_le_quotient_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma ringKrullDim_quotient_minimalPrime_le_quotient_span
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {g : A}
  {P : Ideal A}
  [P.IsPrime]
-- given
  (_hg : g ≠ 0)
  (hP : P ∈ (Ideal.span ({g} : Set A)).minimalPrimes) :
-- imply
  ringKrullDim (A ⧸ P) ≤ ringKrullDim (A ⧸ Ideal.span {g}) := by
-- proof
  apply ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (Ideal.span {g}) r, rfl⟩

/--
[withBot_ENat_add_one_eq_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma withBot_ENat_add_one_eq_coe
  {d : WithBot ℕ∞}
  {n : ℕ}
-- given
  (hn : n ≥ 1)
  (h : (1 : WithBot ℕ∞) + d = ↑(↑n)) :
-- imply
  d = ↑(↑(n - 1) : ℕ∞) := by
-- proof
  cases d with
  | bot => simp at h
  | coe d' =>
    rw [show (1 : WithBot ℕ∞) = ↑(1 : ℕ∞) from rfl, ← WithBot.coe_add] at h
    have h' : (1 : ℕ∞) + d' = ↑n := WithBot.coe_injective h
    cases d' with
    | top => simp at h'
    | coe m =>
      congr 1; congr 1
      have : 1 + m = n := by
        apply @WithTop.coe_injective ℕ (1 + m) n
        push_cast at h' ⊢; exact h'
      omega

/--
[not_irreducible_mvPolynomial_fin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma not_irreducible_mvPolynomial_fin_zero
  {k : Type*}
  [Field k]
  {f : MvPolynomial (Fin 0) k} :
-- imply
  ¬Irreducible f := by
-- proof
  intro hf
  have hiso := (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv
  have hne' : hiso f ≠ 0 := by
    intro h; exact Irreducible.ne_zero hf (hiso.injective (by simp [h]))
  exact hf.not_isUnit (show IsUnit f by
    rw [← hiso.symm_apply_apply f]; exact (IsUnit.mk0 _ hne').map hiso.symm.toRingHom)

/--
[pos_of_irreducible_mvPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma pos_of_irreducible_mvPolynomial
  {k : Type*}
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin n) k}
-- given
  (hf : Irreducible f) :
-- imply
  n ≥ 1 := by
-- proof
  by_contra h
  push Not at h
  interval_cases n
  exact not_irreducible_mvPolynomial_fin_zero k f hf

/--
[height_span_irreducible_mvPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheory.lean)
-/
@[path]
lemma height_span_irreducible_mvPolynomial
  {k : Type*}
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin n) k}
-- given
  (hf : Irreducible f) :
-- imply
  (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).height = 1 := by
-- proof
  haveI : (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).IsPrime := by
    rw [Ideal.span_singleton_prime (Irreducible.ne_zero hf)]
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hmem : Ideal.span ({f} : Set (MvPolynomial (Fin n) k)) ∈
    (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _
  have h_le : (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).height ≤ 1 :=
    height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem
  have h_ne : (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).height ≠ 0 := by
    rw [height_eq_primeHeight]; intro h0
    have := Ideal.primeHeight_eq_zero_iff.mp h0
    change _ ∈ (⊥ : Ideal _).minimalPrimes at this
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at this
    have hbot := Set.mem_singleton_iff.mp this
    have : f ∈ (⊥ : Ideal (MvPolynomial (Fin n) k)) := by
      rw [← hbot]; exact subset_span (Set.mem_singleton f)
    exact Irreducible.ne_zero hf (Ideal.mem_bot.mp this)
  exact le_antisymm h_le (ENat.one_le_iff_ne_zero.mpr h_ne)
/-- Catenarity in the polynomial ring: for a minimal prime `P` of `(g)` with `g ≠ 0`,
`1 + dim(k[x]/P) = dim k[x]`. -/


-- created on 2026-10-23
