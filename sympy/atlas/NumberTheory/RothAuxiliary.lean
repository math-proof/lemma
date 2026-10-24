/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic
set_option maxHeartbeats 999999

/-!
This file contains the auxiliary-polynomial machinery shared by Roth's theorem and Ridout's
S-adic extension. The public theorem abstracts their integrality difference as finite divisibility
data; the ordinary archimedean theorem is the specialization with no divisibility places.
-/

open scoped BigOperators

namespace MathlibExt.NumberTheory.RothAuxiliary

open scoped BigOperators nonZeroDivisors Polynomial

attribute [local instance] Matrix.seminormedAddCommGroup

private abbrev RothMultiIndex (m : ℕ) := Fin m → ℕ

private abbrev RothBox {m : ℕ} (r : Fin m → ℕ) := ∀ h, Fin (r h + 1)

private abbrev RothCoeff {m : ℕ} (r : Fin m → ℕ) := RothBox r → ℤ

private abbrev RothMvIndex (m : ℕ) := Fin m →₀ ℕ

private noncomputable def rothMvHasse {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) (P : MvPolynomial (Fin m) R) : MvPolynomial (Fin m) R :=
  P.coeff.sum fun j c ↦
    MvPolynomial.monomial (j - i) ((∏ h, (Nat.choose (j h) (i h) : R)) * c)

private noncomputable def rothTranslate {R : Type*} [CommRing R] :
    (m : ℕ) → (Fin m → R) →
      MvPolynomial (Fin m) R →+* MvPolynomial (Fin m) R
  | 0, _ => RingHom.id _
  | n + 1, x =>
      (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.toRingHom.comp
        ((Polynomial.mapRingHom (rothTranslate n (fun h ↦ x h.succ))).comp
          ((Polynomial.taylorAlgHom (R := MvPolynomial (Fin n) R)
              (MvPolynomial.C (x 0))).toRingHom.comp
            (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom))

private noncomputable def rothMvWeight {m : ℕ} (r : Fin m → ℕ)
    (i : RothMvIndex m) : ℝ :=
  ∑ h, (i h : ℝ) / r h

private noncomputable def rothRidoutComplement {m : ℕ} (r : Fin m → ℕ)
    (i : RothMvIndex m) : RothMvIndex m :=
  Finsupp.equivFunOnFinite.symm fun h ↦ r h - i h

private def rothMvVanishesBelow {m : ℕ} {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin m) R) (x : Fin m → R) (r : Fin m → ℕ) (t : ℝ) : Prop :=
  ∀ i, rothMvWeight r i < t → (rothTranslate m x P).coeff i = 0

private noncomputable def rothHasseDet {m k : ℕ} {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin m) R) (u v : Fin k → RothMvIndex m) :
    MvPolynomial (Fin m) R :=
  Matrix.det fun s t ↦ rothMvHasse (u s + v t) P

private noncomputable def rothPolyDerivativeRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) (n : ℕ) : Fin k → K[X] :=
  fun j ↦ Polynomial.derivative^[n] (f j)

private def rothPolyJetRows {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) (s : ℕ) : Set (Fin k → K[X]) :=
  {v | ∃ n ≤ s, v = rothPolyDerivativeRow f n}

private noncomputable def rothPolyRowDerivative {k : ℕ} {K : Type*} [Field K]
    (v : Fin k → K[X]) : Fin k → K[X] :=
  fun j ↦ (v j).derivative

private noncomputable def rothPolyWronskianRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) : Fin (k + 1) → K[X] :=
  fun j ↦ Polynomial.wronskian (f 0) (f j)

private noncomputable def rothPolyWronskianDerivativeRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) (n : ℕ) : Fin (k + 1) → K[X] :=
  fun j ↦ Polynomial.derivative^[n] (Polynomial.wronskian (f 0) (f j))

private def rothKroneckerEncode {m : ℕ} (D : ℕ) (i : Fin m → ℕ) : ℕ :=
  ∑ h : Fin m, i h * D ^ (h : ℕ)

private noncomputable def rothKronecker {m : ℕ} {K : Type*} [Field K] (D : ℕ) :
    MvPolynomial (Fin m) K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun h ↦ Polynomial.X ^ D ^ (h : ℕ))

private def rothKroneckerBounded {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (P : MvPolynomial (Fin m) K) : Prop :=
  ∀ i ∈ P.support, ∀ h, i h < D

private def rothMvOrder {m : ℕ} (i : RothMvIndex m) : ℕ :=
  ∑ h, i h

private noncomputable def rothKronHasseRow {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (i : RothMvIndex m) : Fin k → ℚ[X] :=
  fun j ↦ rothKronecker D (rothMvHasse i (f j))

private def rothKronHasseJetRows {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (s : ℕ) : Set (Fin k → ℚ[X]) :=
  {v | ∃ i : RothMvIndex m, rothMvOrder i ≤ s ∧ v = rothKronHasseRow D f i}

private def rothFinsuppL1 {α : Type*} (f : α →₀ ℤ) : ℕ :=
  ∑ a ∈ f.support, (f a).natAbs

private def rothMvL1 {m : ℕ} (P : MvPolynomial (Fin m) ℤ) : ℕ :=
  rothFinsuppL1 P.coeff

private def rothDegreeBound {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (r : Fin m → ℕ) : Prop :=
  ∀ j ∈ P.support, ∀ h, j h ≤ r h

private def rothDegreeBoundOver {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) (r : Fin m → ℕ) : Prop :=
  ∀ j ∈ P.support, ∀ h, j h ≤ r h

private noncomputable def rothLastEquiv (R : Type*) [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans
    (MvPolynomial.optionEquivLeft R (Fin n))

private noncomputable def rothLastIndex {n : ℕ} (i : RothMvIndex n) (a : ℕ) :
    RothMvIndex (n + 1) :=
  (Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i)

private noncomputable def rothLastTail {n : ℕ} (d : RothMvIndex (n + 1)) :
    RothMvIndex n :=
  ((Finsupp.equivCongrLeft finSuccEquivLast) d).some

private noncomputable def rothLastSlice {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : RothMvIndex n) : ℤ[X] :=
  ∑ a ∈ (rothLastEquiv ℤ n P).support,
    Polynomial.monomial a (((rothLastEquiv ℤ n P).coeff a).coeff i)

private structure RothDeterminantData {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (r : Fin (n + 1) → ℕ) where
  k : ℕ
  k_pos : 0 < k
  k_le : k ≤ r (Fin.last n) + 1
  row : Fin k → RothMvIndex n
  row_order : ∀ s, rothMvOrder (row s) ≤ s
  V : MvPolynomial (Fin n) ℤ
  W : ℚ[X]
  U : MvPolynomial (Fin (n + 1)) ℤ
  V_ne : V ≠ 0
  W_ne : W ≠ 0
  U_def : U = rothHasseDet P
    (fun s ↦ rothLastIndex (row s) 0)
    (fun t ↦ rothLastIndex 0 t.val)
  factorization :
    rothLastEquiv ℚ n (MvPolynomial.map (algebraMap ℤ ℚ) U) =
      Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) V) *
        Polynomial.map MvPolynomial.C W
  V_degree : rothDegreeBound V (fun h ↦ k * r h.castSucc)
  U_degree : rothDegreeBound U (fun h ↦ k * r h)
  V_l1 : rothMvL1 V ≤
    k.factorial * (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ k
  U_l1 : rothMvL1 U ≤
    k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ k

private def rothPolyL1 (P : ℤ[X]) : ℕ :=
  rothFinsuppL1 P.toFinsupp.coeff

private structure RothIntegralFactorData {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) where
  coeffIndex : RothMvIndex n
  coeff_ne : d.V.coeff coeffIndex ≠ 0
  WZ : ℤ[X]
  WZ_ne : WZ ≠ 0
  WZ_degree : WZ.natDegree ≤ d.k * r (Fin.last n)
  WZ_l1 : rothPolyL1 WZ ≤
    (d.k * r (Fin.last n) + 1) *
      (d.k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k)
  scaled_factorization :
    rothLastEquiv ℚ n
        ((d.V.coeff coeffIndex : ℚ) •
          MvPolynomial.map (algebraMap ℤ ℚ) d.U) =
      Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) d.V) *
        Polynomial.map MvPolynomial.C
          (Polynomial.map (algebraMap ℤ ℚ) WZ)

private noncomputable def rothBoxIndex {m : ℕ} {r : Fin m → ℕ}
    (j : RothBox r) : RothMvIndex m :=
  Finsupp.equivFunOnFinite.symm fun h ↦ j h

private noncomputable def rothMvOfCoeff {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r) :
    MvPolynomial (Fin m) ℤ :=
  ∑ j, MvPolynomial.monomial (rothBoxIndex j) (c j)

private noncomputable def rothPowerCoord (g : ℤ[X]) : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 =>
      Polynomial.X * rothPowerCoord g n -
        Polynomial.C ((rothPowerCoord g n).coeff (g.natDegree - 1)) * g

private noncomputable def rothHasseEval {m : ℕ} {R : Type*} [CommRing R]
    {r : Fin m → ℕ} (c : RothCoeff r) (i : RothMultiIndex m) (x : Fin m → R) : R :=
  ∑ j, (c j : R) * ∏ h, (Nat.choose (j h) (i h) : R) * x h ^ (j h - i h)

private noncomputable def rothEval {m : ℕ} {R : Type*} [CommRing R]
    {r : Fin m → ℕ} (c : RothCoeff r) (x : Fin m → R) : R :=
  ∑ j, (c j : R) * ∏ h, x h ^ (j h : ℕ)

private noncomputable def rothWeight {m : ℕ} (r : Fin m → ℕ)
    (i : RothMultiIndex m) : ℝ :=
  ∑ h, (i h : ℝ) / r h

private def rothRidoutBoxComplement {m : ℕ} (r : Fin m → ℕ) (j : RothBox r) :
    RothBox r :=
  fun h ↦ ⟨r h - j h, Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩

private noncomputable def rothCentered {m : ℕ} (r : Fin m → ℕ)
    (j : RothBox r) (h : Fin m) : ℝ :=
  (j h : ℝ) / r h - 1 / 2

private noncomputable def rothCenteredSum {m : ℕ} (r : Fin m → ℕ)
    (j : RothBox r) : ℝ :=
  ∑ h, rothCentered r j h

private def rothFlip {m : ℕ} (r : Fin m → ℕ) (h : Fin m) (j : RothBox r) :
    RothBox r :=
  Function.update j h ⟨r h - j h, Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩

private theorem rothFlip_apply_same {m : ℕ} (r : Fin m → ℕ) (h : Fin m)
    (j : RothBox r) :
    ((rothFlip r h j) h : ℕ) = r h - j h := by
  simp [rothFlip]

private theorem rothFlip_apply_ne {m : ℕ} (r : Fin m → ℕ) {h k : Fin m}
    (hhk : k ≠ h) (j : RothBox r) :
    rothFlip r h j k = j k := by
  simp [rothFlip, hhk]

private theorem rothFlip_involutive {m : ℕ} (r : Fin m → ℕ) (h : Fin m) :
    Function.Involutive (rothFlip r h) := by
  intro j
  funext k
  by_cases hkh : k = h
  · subst k
    apply Fin.ext
    rw [rothFlip_apply_same, rothFlip_apply_same]
    have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
    omega
  · rw [rothFlip_apply_ne r hkh, rothFlip_apply_ne r hkh]

private noncomputable def rothFlipEquiv {m : ℕ} (r : Fin m → ℕ) (h : Fin m) :
    RothBox r ≃ RothBox r :=
  (rothFlip_involutive r h).toPerm (rothFlip r h)

private theorem rothCentered_flip_same {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (h : Fin m) (j : RothBox r) :
    rothCentered r (rothFlip r h j) h = -rothCentered r j h := by
  unfold rothCentered
  rw [rothFlip_apply_same]
  have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
  rw [Nat.cast_sub hjle]
  have hrR : (0 : ℝ) < r h := by exact_mod_cast hr h
  field_simp
  ring

private theorem rothCentered_flip_ne {m : ℕ} {r : Fin m → ℕ}
    {h k : Fin m} (hhk : k ≠ h) (j : RothBox r) :
    rothCentered r (rothFlip r h j) k = rothCentered r j k := by
  simp only [rothCentered, rothFlip_apply_ne r hhk]

private theorem rothCentered_cross_sum {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) {h k : Fin m} (hhk : h ≠ k) :
    ∑ j : RothBox r, rothCentered r j h * rothCentered r j k = 0 := by
  have hreindex := Equiv.sum_comp (rothFlipEquiv r h)
    (fun j : RothBox r ↦ rothCentered r j h * rothCentered r j k)
  have hkh : k ≠ h := Ne.symm hhk
  have hneg :
      (∑ j : RothBox r,
          rothCentered r (rothFlip r h j) h * rothCentered r (rothFlip r h j) k) =
        -(∑ j : RothBox r, rothCentered r j h * rothCentered r j k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [rothCentered_flip_same hr, rothCentered_flip_ne hkh]
    ring
  change
    (∑ j : RothBox r,
        rothCentered r (rothFlip r h j) h * rothCentered r (rothFlip r h j) k) =
      ∑ j : RothBox r, rothCentered r j h * rothCentered r j k at hreindex
  rw [hneg] at hreindex
  linarith

private theorem rothCentered_second_moment_le {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) :
    ∑ j : RothBox r, rothCenteredSum r j ^ 2 ≤
      (m : ℝ) * Fintype.card (RothBox r) / 4 := by
  have hexpand :
      (∑ j : RothBox r, rothCenteredSum r j ^ 2) =
        ∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
          rothCentered r j h * rothCentered r j k := by
    calc
      (∑ j : RothBox r, rothCenteredSum r j ^ 2) =
          ∑ j : RothBox r, ∑ h : Fin m, ∑ k : Fin m,
            rothCentered r j h * rothCentered r j k := by
        apply Finset.sum_congr rfl
        intro j _hj
        unfold rothCenteredSum
        rw [pow_two, Finset.sum_mul_sum]
      _ = ∑ h : Fin m, ∑ j : RothBox r, ∑ k : Fin m,
            rothCentered r j h * rothCentered r j k := Finset.sum_comm
      _ = ∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
            rothCentered r j h * rothCentered r j k := by
        apply Finset.sum_congr rfl
        intro h _hh
        exact Finset.sum_comm
  rw [hexpand]
  calc
    (∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
        rothCentered r j h * rothCentered r j k) ≤
        ∑ h : Fin m, ∑ k : Fin m,
          if h = k then (Fintype.card (RothBox r) : ℝ) / 4 else 0 := by
      gcongr with h k
      by_cases hhk : h = k
      · subst k
        simpa [pow_two] using rothCentered_sq_sum_le hr h
      · simp only [hhk, ↓reduceIte]
        rw [rothCentered_cross_sum hr hhk]
    _ = (m : ℝ) * Fintype.card (RothBox r) / 4 := by
      simp
      ring

private noncomputable def rothLowIndices {m : ℕ} (r : Fin m → ℕ) (γ : ℝ) :
    Finset (RothBox r) :=
  Finset.univ.filter fun i ↦
    rothWeight r (fun h ↦ i h) < (m : ℝ) * (1 / 2 - γ)

private theorem roth_low_indices_card_bound {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ) :
    (4 : ℝ) * m * γ ^ 2 * (rothLowIndices r γ).card ≤
      Fintype.card (RothBox r) := by
  let L := rothLowIndices r γ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpoint : ∀ j ∈ L,
      ((m : ℝ) * γ) ^ 2 ≤ rothCenteredSum r j ^ 2 := by
    intro j hj
    have hjlow := (Finset.mem_filter.mp hj).2
    rw [rothWeight_eq_centeredSum_add] at hjlow
    have hs : rothCenteredSum r j < -((m : ℝ) * γ) := by linarith
    have hmg : 0 < (m : ℝ) * γ := mul_pos hmR hγ
    nlinarith
  have hlow :
      (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 ≤
        ∑ j ∈ L, rothCenteredSum r j ^ 2 := by
    calc
      (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 =
          ∑ _j ∈ L, ((m : ℝ) * γ) ^ 2 := by simp
      _ ≤ ∑ j ∈ L, rothCenteredSum r j ^ 2 := by
        exact Finset.sum_le_sum fun j hj ↦ hpoint j hj
  have hsubset :
      (∑ j ∈ L, rothCenteredSum r j ^ 2) ≤
        ∑ j : RothBox r, rothCenteredSum r j ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro j _hj _hjL
      positivity
  have hmain :
      (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 ≤
        (m : ℝ) * Fintype.card (RothBox r) / 4 :=
    hlow.trans (hsubset.trans (rothCentered_second_moment_le hr))
  have hmul :
      (m : ℝ) * ((4 : ℝ) * m * γ ^ 2 * L.card) ≤
        (m : ℝ) * Fintype.card (RothBox r) := by
    calc
      (m : ℝ) * ((4 : ℝ) * m * γ ^ 2 * L.card) =
          4 * ((L.card : ℝ) * ((m : ℝ) * γ) ^ 2) := by ring
      _ ≤ 4 * ((m : ℝ) * Fintype.card (RothBox r) / 4) := by
        gcongr
      _ = (m : ℝ) * Fintype.card (RothBox r) := by ring
  exact (mul_le_mul_iff_of_pos_left hmR).mp hmul

private abbrev RothLowIndex {m : ℕ} (r : Fin m → ℕ) (γ : ℝ) :=
  {i : RothBox r // i ∈ rothLowIndices r γ}

private theorem roth_low_equation_card_lt {m d : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ)
    (hparam : (d : ℝ) < 4 * m * γ ^ 2) :
    Fintype.card (RothLowIndex r γ × Fin d) < Fintype.card (RothBox r) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  by_cases hL : (rothLowIndices r γ).card = 0
  · simp only [hL, zero_mul]
    exact Fintype.card_pos_iff.mpr
      ⟨fun h ↦ ⟨0, Nat.succ_pos (r h)⟩⟩
  · have hLpos : (0 : ℝ) < (rothLowIndices r γ).card := by
      exact_mod_cast Nat.pos_of_ne_zero hL
    have hstrict :
        (d : ℝ) * (rothLowIndices r γ).card <
          (4 * m * γ ^ 2) * (rothLowIndices r γ).card :=
      mul_lt_mul_of_pos_right hparam hLpos
    have hbound := roth_low_indices_card_bound hr hm hγ
    have hreal :
        ((d * (rothLowIndices r γ).card : ℕ) : ℝ) <
          Fintype.card (RothBox r) := by
      norm_num only [Nat.cast_mul]
      exact hstrict.trans_le hbound
    have hnat : d * (rothLowIndices r γ).card < Fintype.card (RothBox r) := by
      exact_mod_cast hreal
    simpa [mul_comm] using hnat

private def rothZeroBox {m : ℕ} (r : Fin m → ℕ) : RothBox r :=
  fun h ↦ ⟨0, Nat.succ_pos (r h)⟩

private theorem roth_low_equation_twice_card_le {m d : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ)
    (hparam : (d : ℝ) ≤ 2 * m * γ ^ 2) :
    2 * Fintype.card (RothLowIndex r γ × Fin d) ≤ Fintype.card (RothBox r) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  have hbound := roth_low_indices_card_bound hr hm hγ
  have hreal :
      ((2 * ((rothLowIndices r γ).card * d) : ℕ) : ℝ) ≤
        Fintype.card (RothBox r) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (2 : ℝ) * ((rothLowIndices r γ).card * d) =
          (2 * d) * (rothLowIndices r γ).card := by ring
      _ ≤ (4 * m * γ ^ 2) * (rothLowIndices r γ).card := by
        have hcoef : (2 : ℝ) * d ≤ 4 * m * γ ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ Fintype.card (RothBox r) := hbound
  exact_mod_cast hreal

private def rothVanishesBelow {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r)
    (x : Fin m → ℝ) (t : ℝ) : Prop :=
  ∀ i, rothWeight r i < t → rothHasseEval c i x = 0

private noncomputable def rothDenProduct {m : ℕ} (q : Fin m → ℚ)
    (r : Fin m → ℕ) : ℕ :=
  ∏ h, (q h).den ^ r h

private noncomputable def rothClearEval {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (q : Fin m → ℚ) (r : Fin m → ℕ) : ℤ :=
  ∑ d ∈ P.support, P.coeff d *
    ∏ h, (q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)

private def rothRidoutExponent {m : ℕ} {ι : Type*} (r : Fin m → ℕ)
    (a b : Fin m → ι → ℕ) (k : RothMvIndex m) (l : ι) : ℕ :=
  ∑ h, (a h l * k h + b h l * (r h - k h))

private noncomputable def rothIntPolynomial (α : ℝ) : ℤ[X] :=
  IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α)

private noncomputable def rothIntegralPolynomial (α : ℝ) : ℤ[X] :=
  (rothIntPolynomial α).integralNormalization

private noncomputable def rothCoordinateBase (α : ℝ) : ℕ :=
  max (rothIntPolynomial α).leadingCoeff.natAbs
    (rothPolyL1 (rothIntegralPolynomial α) + 1)

private noncomputable def rothScaledPowerCoord (α : ℝ) (S n : ℕ) : ℤ[X] :=
  Polynomial.C ((rothIntPolynomial α).leadingCoeff ^ (S - n)) *
    rothPowerCoord (rothIntegralPolynomial α) n

private noncomputable def rothTermDegree {m : ℕ} {r : Fin m → ℕ}
    (i j : RothBox r) : ℕ :=
  ∑ h, ((j h : ℕ) - (i h : ℕ))

private noncomputable def rothAuxTerm (α : ℝ) {m : ℕ} {r : Fin m → ℕ}
    (i j : RothBox r) : ℤ[X] :=
  Polynomial.C (∏ h, (Nat.choose (j h) (i h) : ℤ)) *
    rothScaledPowerCoord α (∑ h, r h) (rothTermDegree i j)

private noncomputable def rothAuxMatrix (α : ℝ) {m : ℕ} (r : Fin m → ℕ) (γ : ℝ) :
    Matrix (RothLowIndex r γ × Fin (rothIntegralPolynomial α).natDegree)
      (RothBox r) ℤ :=
  fun u j ↦ (rothAuxTerm α u.1.1 j).coeff u.2

private noncomputable def rothRidoutAuxMatrix (α : ℝ) {m : ℕ}
    (r : Fin m → ℕ) (γ : ℝ) :
    Matrix (RothLowIndex r γ × Fin ((rothIntegralPolynomial α).natDegree + 2))
      (RothBox r) ℤ :=
  fun u j ↦
    Fin.lastCases
      (if j = rothRidoutBoxComplement r u.1.1 then 1 else 0)
      (fun v ↦ Fin.lastCases
        (if j = u.1.1 then 1 else 0)
        (fun k ↦ rothAuxMatrix α r γ (u.1, k) j) v) u.2

private noncomputable def rothAuxCombination (α : ℝ) {m : ℕ} {r : Fin m → ℕ}
    (i : RothBox r) (c : RothCoeff r) : ℤ[X] :=
  ∑ j, Polynomial.C (c j) * rothAuxTerm α i j

private theorem roth_ridout_exists_auxiliary_coeff
    (α : ℝ) (hα : IsAlgebraic ℚ α) {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ0 : 0 < γ) (hγhalf : γ < 1 / 2)
    (hparamStrict : (((rothIntegralPolynomial α).natDegree + 2 : ℕ) : ℝ) <
      4 * m * γ ^ 2)
    (hparamHalf : (((rothIntegralPolynomial α).natDegree + 2 : ℕ) : ℝ) ≤
      2 * m * γ ^ 2) :
    ∃ c : RothCoeff r, c ≠ 0 ∧
      rothVanishesBelow c (fun _h ↦ α) ((m : ℝ) * (1 / 2 - γ)) ∧
      (∀ j, c j ≠ 0 →
        (m : ℝ) * (1 / 2 - γ) ≤ rothWeight r (fun h ↦ j h) ∧
          rothWeight r (fun h ↦ j h) ≤
            (m : ℝ) - (m : ℝ) * (1 / 2 - γ)) ∧
      rothMvL1 (rothMvOfCoeff c) ≤
        (8 * rothCoordinateBase α) ^ (∑ h, r h) := by
  let d := (rothIntegralPolynomial α).natDegree + 2
  let A := rothRidoutAuxMatrix α r γ
  let M := Fintype.card (RothLowIndex r γ × Fin d)
  let N := Fintype.card (RothBox r)
  let S := ∑ h, r h
  let H := (2 * rothCoordinateBase α) ^ S
  have hd : 0 < d := by dsimp [d]; omega
  have hcard : M < N := by
    exact roth_low_equation_card_lt hr hm hγ0 hparamStrict
  have hMpos : 0 < M := roth_low_equation_card_pos hm hd hγhalf
  have htwice : 2 * M ≤ N := by
    exact roth_low_equation_twice_card_le hr hm hγ0 hparamHalf
  obtain ⟨c, hc, hker, hcnorm⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le A hcard hMpos
  have hcardR : (M : ℝ) < N := by exact_mod_cast hcard
  have htwiceR : (2 : ℝ) * M ≤ N := by exact_mod_cast htwice
  have hden : 0 < (N : ℝ) - M := sub_pos.mpr hcardR
  have hexp : (M : ℝ) / ((N : ℝ) - M) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hcard
  have hbase : (1 : ℝ) ≤ (N : ℝ) * max 1 ‖A‖ := by
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hNpos)
      (le_max_left _ _)
  have hrpow :
      ((N : ℝ) * max 1 ‖A‖) ^ ((M : ℝ) / ((N : ℝ) - M)) ≤
        (N : ℝ) * max 1 ‖A‖ := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hHnat : 1 ≤ H := by
    apply one_le_pow₀
    have hB := rothCoordinateBase_pos α
    omega
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hHnat
  have hAnorm : ‖A‖ ≤ (H : ℝ) := by
    exact rothRidoutAuxMatrix_norm_le α r γ
  have hmax : max 1 ‖A‖ ≤ (H : ℝ) := max_le hH hAnorm
  have hcnormSimple : ‖c‖ ≤ (N : ℝ) * H := by
    calc
      ‖c‖ ≤ ((N : ℝ) * max 1 ‖A‖) ^ ((M : ℝ) / ((N : ℝ) - M)) := hcnorm
      _ ≤ (N : ℝ) * max 1 ‖A‖ := hrpow
      _ ≤ (N : ℝ) * H := by gcongr
  have hsumNorm := Pi.sum_norm_apply_le_norm c
  have hsum : ((∑ j, (c j).natAbs : ℕ) : ℝ) ≤ (N : ℝ) * ‖c‖ := by
    calc
      ((∑ j, (c j).natAbs : ℕ) : ℝ) = ∑ j, ((c j).natAbs : ℝ) := by
        norm_cast
      _ = ∑ j, ‖c j‖ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs]
        norm_num
      _ ≤ (N : ℝ) * ‖c‖ := by
        simpa [N, nsmul_eq_mul] using hsumNorm
  have hN : N ≤ 2 ^ S := roth_box_card_le_two_pow_sum hr
  have hl1Nat := rothMvL1_ofCoeff_le c
  have hl1 : (rothMvL1 (rothMvOfCoeff c) : ℝ) ≤
      (((8 * rothCoordinateBase α) ^ S : ℕ) : ℝ) := by
    calc
      (rothMvL1 (rothMvOfCoeff c) : ℝ) ≤ (∑ j, (c j).natAbs : ℕ) := by
        exact_mod_cast hl1Nat
      _ ≤ (N : ℝ) * ‖c‖ := hsum
      _ ≤ (N : ℝ) * ((N : ℝ) * H) := by gcongr
      _ ≤ ((2 ^ S : ℕ) : ℝ) * (((2 ^ S : ℕ) : ℝ) * H) := by gcongr
      _ = (((8 * rothCoordinateBase α) ^ S : ℕ) : ℝ) := by
        norm_cast
        dsimp [H]
        rw [← mul_pow, ← mul_pow]
        congr 1
        ring
  have hkerOld := roth_ridout_old_mulVec_eq_zero α c hker
  refine ⟨c, hc, ?_, ?_, by exact_mod_cast hl1⟩
  · intro i hi
    by_cases hir : ∀ h, i h ≤ r h
    · let ib : RothBox r := fun h ↦ ⟨i h, Nat.lt_succ_iff.mpr (hir h)⟩
      have hibLow : ib ∈ rothLowIndices r γ := by
        simp only [rothLowIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [ib] using hi
      exact rothHasseEval_eq_zero_of_mulVec_eq_zero α hα ⟨ib, hibLow⟩ c hkerOld
    · push Not at hir
      obtain ⟨h, hh⟩ := hir
      unfold rothHasseEval
      apply Finset.sum_eq_zero
      intro j _hj
      have hjlt : (j h : ℕ) < i h :=
        lt_of_le_of_lt (Nat.le_of_lt_succ (j h).isLt) hh
      have hz : (Nat.choose (j h) (i h) : ℝ) = 0 := by
        simp [Nat.choose_eq_zero_of_lt hjlt]
      rw [Finset.prod_eq_zero (Finset.mem_univ h)]
      · ring
      · rw [hz]
        simp
  · intro j hj
    exact roth_ridout_coeff_weight_bounds α c hr hker j hj

private structure RothLemmaInput (n : ℕ) (δ : ℝ) (Q R : ℕ) where
  P : MvPolynomial (Fin (n + 1)) ℤ
  r : Fin (n + 1) → ℕ
  q : Fin (n + 1) → ℚ
  P_ne : P ≠ 0
  P_degree : rothDegreeBound P r
  r_large : ∀ h, R ≤ r h
  den_large : Q ≤ (q 0).den
  den_monotone : Monotone fun h ↦ (q h).den
  r_antitone : Antitone r
  separated : ∀ i : Fin n, (r i.succ : ℝ) ≤ δ * r i.castSucc
  den_power : ∀ h, (q 0).den ^ r 0 ≤ (q h).den ^ r h
  height : (rothMvL1 P : ℝ) ≤ Real.rpow (q 0).den (δ * r 0)

private theorem roth_ridout_finite_approximations_small_exponent
    (α : ℝ) (hα : IsAlgebraic ℚ α) (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    {ι : Type*} (S : Finset ι) (p : ι → ℕ) (μ ν : ι → ℝ)
    (hμ : ∀ l ∈ S, 0 ≤ μ l) (hν : ∀ l ∈ S, 0 ≤ ν l)
    (hσ : ∑ l ∈ S, (μ l + ν l) < 2 + ε) :
    Set.Finite {q : ℚ |
      |α - (q : ℝ)| <
          1 / Real.rpow (q.den : ℝ) (2 + ε - ∑ l ∈ S, (μ l + ν l)) ∧
        ∃ a b : ι → ℕ,
          ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
          (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
          ∀ l ∈ S,
            Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
            Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l} := by
  classical
  let σ := ∑ l ∈ S, (μ l + ν l)
  let A : Set ℚ := {q : ℚ |
    |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) (2 + ε - σ) ∧
      ∃ a b : ι → ℕ,
        ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
        (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
        ∀ l ∈ S,
          Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
          Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l}
  change A.Finite
  by_contra hinf
  let γ := ε / 16
  let θ := ε / 16
  let η := ε / 16
  let aR := 2 + ε
  let a := aR - σ
  let D := (rothIntegralPolynomial α).natDegree
  let n := ⌈(((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2))⌉₊
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγhalf : γ < 1 / 2 := by dsimp [γ]; linarith
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθone : θ ≤ 1 := by dsimp [θ]; linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hD : 0 < D := rothIntegralPolynomial_natDegree_pos hα
  have hdenom : 0 < 2 * γ ^ 2 := by positivity
  have hnceil : (((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2)) ≤ n := Nat.le_ceil _
  have hnR : 0 < (n : ℝ) :=
    (div_pos (by positivity) hdenom).trans_le hnceil
  have hn : 0 < n := by exact_mod_cast hnR
  have hparamHalf : (((D + 2 : ℕ) : ℝ)) ≤ 2 * (n + 1 : ℕ) * γ ^ 2 := by
    have hbase : (((D + 2 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) * γ ^ 2 := by
      calc
        (((D + 2 : ℕ) : ℝ)) =
            (2 * γ ^ 2) * (((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2)) := by
              field_simp
        _ ≤ (2 * γ ^ 2) * n := mul_le_mul_of_nonneg_left hnceil hdenom.le
        _ = 2 * (n : ℝ) * γ ^ 2 := by ring
    calc
      (((D + 2 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) * γ ^ 2 := hbase
      _ ≤ 2 * (n + 1 : ℕ) * γ ^ 2 := by
        push_cast
        nlinarith [sq_nonneg γ]
  have hparamStrict : (((D + 2 : ℕ) : ℝ)) < 4 * (n + 1 : ℕ) * γ ^ 2 := by
    have hpos : 0 < 2 * (n + 1 : ℕ) * γ ^ 2 := by positivity
    nlinarith
  obtain ⟨δ, Q, R, hδ, hδone, hQtwo, hRone, hRoth⟩ :=
    roth_lemma n θ hθ hθone
  let β := min δ (1 / (2 * (n + 1 : ℕ)))
  have hβ : 0 < β := lt_min hδ (by positivity)
  have hβδ : β ≤ δ := min_le_left _ _
  have hβn : (n : ℝ) * β ≤ 1 := by
    have hβfrac : β ≤ 1 / (2 * (n + 1 : ℕ)) := min_le_right _ _
    calc
      (n : ℝ) * β ≤ (n : ℝ) * (1 / (2 * (n + 1 : ℕ))) :=
        mul_le_mul_of_nonneg_left hβfrac (Nat.cast_nonneg _)
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        push_cast
        nlinarith
  let K := ⌈2 / β⌉₊
  have hK : 2 ≤ β * K := by
    have hc : 2 / β ≤ (K : ℝ) := Nat.le_ceil _
    calc
      (2 : ℝ) = β * (2 / β) := by field_simp
      _ ≤ β * K := mul_le_mul_of_nonneg_left hc hβ.le
  have hKpos : 0 < K := by
    by_contra hnot
    have hz : K = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.cast_zero, mul_zero] at hK
    norm_num at hK
  let T := (n + 1 : ℕ) * (1 / 2 - γ)
  let g := aR * (T - θ) - (n + 1 : ℕ) * (1 + η)
  have hgform : g = ε / 16 * ((5 - ε) * (n + 1 : ℕ) - (2 + ε)) := by
    dsimp [g, aR, T, θ, η, γ]
    push_cast
    ring
  have hg : 0 < g := by
    rw [hgform]
    have hfive : 0 ≤ 5 - ε := by linarith
    have hmul : 5 - ε ≤ (5 - ε) * (n + 1 : ℕ) := by
      have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 n)
      nlinarith
    have hbracket : 0 < (5 - ε) * (n + 1 : ℕ) - (2 + ε) := by
      nlinarith
    positivity
  let H : ℕ := 8 * rothCoordinateBase α
  let C : ℝ := 8 * H * max 1 |α|
  have hH : 1 ≤ H := by
    dsimp [H]
    have := rothCoordinateBase_pos α
    omega
  have hC : 1 ≤ C := by
    dsimp [C]
    have hmax : (1 : ℝ) ≤ max 1 |α| := le_max_left _ _
    have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith
  obtain ⟨QH, hQH⟩ := roth_exists_rpow_threshold_of ((H : ℝ) ^ 2) hδ
  obtain ⟨QC, hQC⟩ := roth_exists_rpow_threshold_of (C ^ 2) (by positivity : 0 < g / 2)
  let N := max Q (max 2 (max QH QC))
  have hQN : Q ≤ N := le_max_left _ _
  have htwoN : 2 ≤ N :=
    (le_max_left 2 (max QH QC)).trans (le_max_right Q (max 2 (max QH QC)))
  have hQHN : QH ≤ N :=
    (le_max_left QH QC).trans (le_max_right 2 (max QH QC)) |>.trans
      (le_max_right Q (max 2 (max QH QC)))
  have hQCN : QC ≤ N :=
    (le_max_right QH QC).trans (le_max_right 2 (max QH QC)) |>.trans
      (le_max_right Q (max 2 (max QH QC)))
  have ha : 0 < a := by
    dsimp [a, aR, σ]
    linarith
  have hAsub : A ⊆ {q : ℚ |
      |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) a} := by
    intro q hq
    simpa [A, a] using hq.1
  obtain ⟨q, hqA, hq0N, hchain⟩ :=
    roth_ridout_exists_approximation_chain (α := α) (p := a) ha A hAsub hinf
      n N K
  have happrox : ∀ h,
      |α - (q h : ℝ)| < 1 / Real.rpow ((q h).den : ℝ) a :=
    fun h ↦ hAsub (hqA h)
  have hwit : ∀ h, ∃ av bv : ι → ℕ,
      ((∏ l ∈ S, p l ^ av l : ℕ) : ℤ) ∣ (q h).num ∧
      (∏ l ∈ S, p l ^ bv l) ∣ (q h).den ∧
      ∀ l ∈ S,
        Real.rpow ((q h).den : ℝ) (μ l) ≤ (p l : ℝ) ^ av l ∧
        Real.rpow ((q h).den : ℝ) (ν l) ≤ (p l : ℝ) ^ bv l := by
    intro h
    exact (hqA h).2
  choose av bv hav using hwit
  let d : Fin (n + 1) → ℕ := fun h ↦ (q h).den
  have hKone : 1 ≤ K := hKpos
  have hdstep : ∀ i : Fin n, d i.castSucc ≤ d i.succ := by
    intro i
    calc
      d i.castSucc = d i.castSucc ^ 1 := (pow_one _).symm
      _ ≤ d i.castSucc ^ K :=
        pow_le_pow_right₀ (q i.castSucc).pos hKone
      _ ≤ d i.succ := (hchain i).le
  have hdmono : Monotone d := Fin.monotone_iff_le_succ.mpr hdstep
  have hd0two : 2 ≤ d 0 := htwoN.trans hq0N.le
  have hd : ∀ h, 2 ≤ d h := fun h ↦ hd0two.trans (hdmono (Fin.zero_le h))
  obtain ⟨r, hrlarge, hranti, hsep, hpower, hsum, hupper⟩ :=
    roth_exists_balanced_degrees d K R δ β η hd hdmono hchain
      hβ hβδ hη hβn hK
  have hrpos : ∀ h, 0 < r h := fun h ↦
    lt_of_lt_of_le Nat.zero_lt_one (hRone.trans (hrlarge h))
  obtain ⟨c, hc, hcvan, hcbalanced, hcl1⟩ :=
    roth_ridout_exists_auxiliary_coeff α hα hrpos
      (by omega : 0 < n + 1) hγ hγhalf
      (by simpa [D] using hparamStrict) (by simpa [D] using hparamHalf)
  let P := rothMvOfCoeff c
  have hPne : P ≠ 0 := rothMvOfCoeff_ne_zero hc
  have hPdegree : rothDegreeBound P r := rothMvOfCoeff_degreeBound c
  have hPvan : rothMvVanishesBelow
      (MvPolynomial.map (algebraMap ℤ ℝ) P) (fun _h ↦ α) r T := by
    exact rothVanishesBelow_to_mv hcvan
  have hheight : (rothMvL1 P : ℝ) ≤
      Real.rpow (q 0).den (δ * r 0) := by
    have hbase : (H : ℝ) ^ 2 ≤ Real.rpow (q 0).den δ :=
      hQH _ (hQHN.trans hq0N.le)
    calc
      (rothMvL1 P : ℝ) ≤ ((H ^ (∑ h, r h) : ℕ) : ℝ) := by
        exact_mod_cast hcl1
      _ = (H : ℝ) ^ (∑ h, r h) := by norm_cast
      _ ≤ Real.rpow (q 0).den (δ * r 0) :=
        roth_pow_le_rpow_of_le_twice H (q 0).den δ (∑ h, r h) (r 0)
          (by exact_mod_cast hH) (by positivity) hsum hbase
  let Q₀ : ℝ := ((q 0).den : ℝ) ^ r 0
  have hQ₀ : 1 < Q₀ := by
    dsimp [Q₀]
    apply one_lt_pow₀
    · exact_mod_cast hd0two
    · exact (hrpos 0).ne'
  have hpowerR : ∀ h, Q₀ ≤ ((q h).den : ℝ) ^ r h := by
    intro h
    dsimp [Q₀]
    exact_mod_cast hpower h
  have herr : ∀ l : RothMvIndex (n + 1),
      ∏ h, |(q h : ℝ) - α| ^ l h ≤
        Real.rpow Q₀ (-a * rothMvWeight r l) := by
    exact roth_product_approximation_bound_of_den_power (fun _h ↦ α) q r hrpos
      a Q₀ ha.le (zero_lt_one.trans hQ₀) hpowerR happrox
  have hdenUpper : (rothDenProduct q r : ℝ) ≤
      Real.rpow Q₀ ((n + 1 : ℕ) * (1 + η)) := by
    apply roth_denProduct_le_rpow q r Q₀ η (zero_le_one.trans hQ₀.le)
    intro h
    simpa [Q₀, d] using hupper h
  let F : ℝ :=
    (((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
      ∏ _h : Fin (n + 1), max 1 |α| ^ r _h)
  have hFnonneg : 0 ≤ F := by dsimp [F]; positivity
  have hF : F ≤ Real.rpow Q₀ (g / 2) := by
    have hCbase : C ^ 2 ≤ Real.rpow (q 0).den (g / 2) :=
      hQC _ (hQCN.trans hq0N.le)
    have hCpow : C ^ (∑ h, r h) ≤
        Real.rpow (q 0).den ((g / 2) * r 0) :=
      roth_pow_le_rpow_of_le_twice C (q 0).den (g / 2) (∑ h, r h) (r 0)
        hC (by positivity) hsum hCbase
    have hraw : F ≤ C ^ (∑ h, r h) := by
      dsimp [F, C]
      rw [Finset.prod_pow_eq_pow_sum]
      have hcl1R : (rothMvL1 P : ℝ) ≤ (H : ℝ) ^ (∑ h, r h) := by
        exact_mod_cast hcl1
      calc
        ((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
              max 1 |α| ^ (∑ h, r h) ≤
            ((8 : ℝ) ^ (∑ h, r h) * (H : ℝ) ^ (∑ h, r h)) *
              max 1 |α| ^ (∑ h, r h) := by
                push_cast
                gcongr
        _ = (8 * (H : ℝ) * max 1 |α|) ^ (∑ h, r h) := by
          rw [mul_pow, mul_pow]
    refine hraw.trans (hCpow.trans_eq ?_)
    dsimp [Q₀]
    calc
      Real.rpow (q 0).den ((g / 2) * r 0) =
          Real.rpow (q 0).den ((r 0 : ℝ) * (g / 2)) := by congr 1; ring
      _ = Real.rpow (Real.rpow (q 0).den (r 0 : ℝ)) (g / 2) :=
        Real.rpow_mul (by positivity) _ _
      _ = Real.rpow (((q 0).den : ℝ) ^ r 0) (g / 2) := by
        congr 1
        exact Real.rpow_natCast _ _
  have hmaster : (rothDenProduct q r : ℝ) * F <
      Real.rpow Q₀ (aR * (T - θ)) := by
    apply roth_mul_lt_rpow Q₀ (rothDenProduct q r) F
      ((n + 1 : ℕ) * (1 + η)) (g / 2) (aR * (T - θ)) hQ₀
      hFnonneg hdenUpper hF
    dsimp [g]
    nlinarith
  let s := σ * (T - θ)
  have hdiv : ∀ i : RothMvIndex (n + 1), rothMvWeight r i ≤ θ →
      ∃ G : ℕ, Real.rpow Q₀ s ≤ G ∧
        (G : ℤ) ∣ rothClearEval (rothMvHasse i P) q r := by
    intro i hi
    simpa [P, s, σ] using
      roth_ridout_exists_hasse_clear_divisor S p q r av bv μ ν c Q₀ T θ i
        hrpos hQ₀ hθ.le hμ hν hpowerR
        (fun h ↦ (hav h).1) (fun h ↦ (hav h).2.1)
        (fun h l hl ↦ (hav h).2.2 l hl |>.1)
        (fun h l hl ↦ (hav h).2.2 l hl |>.2)
        hcbalanced hi
  have hmaster' : (rothDenProduct q r : ℝ) *
        (((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
          ∏ h, max 1 |(fun _h : Fin (n + 1) ↦ α) h| ^ r h) <
      Real.rpow Q₀ (s + a * (T - θ)) := by
    rw [show s + a * (T - θ) = aR * (T - θ) by
      dsimp [s, a]
      ring]
    simpa [F] using hmaster
  have hzero := roth_ridout_hasse_eq_zero_at_rational_of_taylor_bound P
    (fun _h ↦ α) q r hrpos hPdegree T a Q₀ θ s hPvan
    ha.le hQ₀ herr hdiv hmaster'
  have hratvan := roth_rational_vanishing_of_real_hasse_zero P q r θ hzero
  let X : RothLemmaInput n δ Q R := {
    P := P
    r := r
    q := q
    P_ne := hPne
    P_degree := hPdegree
    r_large := hrlarge
    den_large := hQN.trans hq0N.le
    den_monotone := by simpa [d] using hdmono
    r_antitone := hranti
    separated := hsep
    den_power := by simpa [d] using hpower
    height := hheight
  }
  exact hRoth X hratvan

/-- Roth's finiteness theorem with an abstract finite collection of divisibility places.

The functions `p`, `μ`, and `ν` encode lower bounds on powers dividing the numerator and
denominator. Taking `S` empty gives the usual archimedean approximation set. -/
theorem finite_of_divisible_approximations
    (α : ℝ) (hα : IsAlgebraic ℚ α)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    {ι : Type*} (S : Finset ι) (p : ι → ℕ) (μ ν : ι → ℝ)
    (hμ : ∀ l ∈ S, 0 ≤ μ l) (hν : ∀ l ∈ S, 0 ≤ ν l)
    (hσ : ∑ l ∈ S, (μ l + ν l) < 2 + ε) :
    Set.Finite {q : ℚ |
      |α - (q : ℝ)| <
          1 / Real.rpow (q.den : ℝ) (2 + ε - ∑ l ∈ S, (μ l + ν l)) ∧
        ∃ a b : ι → ℕ,
          ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
          (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
          ∀ l ∈ S,
            Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
            Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l} :=
  roth_ridout_finite_approximations_small_exponent α hα ε hε hεone
    S p μ ν hμ hν hσ
end MathlibExt.NumberTheory.RothAuxiliary
