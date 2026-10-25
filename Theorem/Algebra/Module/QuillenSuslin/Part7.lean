/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Ring
import Def.Algebra.Module.QuillenSuslin.Part7
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qsMatrixPolynomialPart_transpose
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*}
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R))) :
    qsMatrixPolynomialPart R A.transpose =
      (qsMatrixPolynomialPart R A).transpose :=
  rfl

theorem qsMatrixPolynomialPart_algebraMap
    {R : Type*} [CommRing R] [Nontrivial R]
    {ι κ : Type*} (A : Matrix ι κ (Polynomial R)) :
    qsMatrixPolynomialPart R
        (A.map (algebraMap (Polynomial R)
          (Localization (qsMonicSubmonoid R)))) = A := by
  apply Matrix.ext
  intro i j
  exact qsPolynomialPart_algebraMap (A i j)

theorem qsMatrixPolynomialPart_map_residue
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*}
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)))
    (hAC : A.map (qsResidueMonicMap R) =
      C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
        (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
    (qsMatrixPolynomialPart R A).map
      (Polynomial.mapRingHom (IsLocalRing.residue R)) = C := by
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun hAC i) j
  have hpart := qsPolynomialPart_map_residue R (A i j)
  change qsResidueMonicMap R (A i j) =
    algebraMap (Polynomial (IsLocalRing.ResidueField R))
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) (C i j) at hij
  rw [hij, qsPolynomialPart_algebraMap] at hpart
  exact hpart

theorem qsPolynomialPart_mul_eq_zero
    {R : Type*} [CommRing R] [Nontrivial R]
    {x y : Localization (qsMonicSubmonoid R)}
    (hx : qsPolynomialPart R x = 0)
    (hy : qsPolynomialPart R y = 0) :
    qsPolynomialPart R (x * y) = 0 := by
  induction x using Localization.induction_on with
  | _ x =>
    obtain ⟨a, b⟩ := x
    induction y using Localization.induction_on with
    | _ y =>
      obtain ⟨c, d⟩ := y
      change a /ₘ (b : Polynomial R) = 0 at hx
      change c /ₘ (d : Polynomial R) = 0 at hy
      rw [Localization.mk_mul]
      change (a * c) /ₘ ((b : Polynomial R) * d) = 0
      rw [Polynomial.divByMonic_eq_zero_iff (b.property.mul d.property)]
      by_cases ha : a = 0
      · rw [ha, zero_mul, Polynomial.degree_zero, bot_lt_iff_ne_bot,
          Ne, Polynomial.degree_eq_bot]
        exact (b.property.mul d.property).ne_zero
      by_cases hc : c = 0
      · rw [hc, mul_zero, Polynomial.degree_zero, bot_lt_iff_ne_bot,
          Ne, Polynomial.degree_eq_bot]
        exact (b.property.mul d.property).ne_zero
      exact (Polynomial.degree_mul_le a c).trans_lt <|
        (WithBot.add_lt_add_of_lt_of_le (Polynomial.degree_ne_bot.mpr hc)
          ((Polynomial.divByMonic_eq_zero_iff b.property).mp hx)
          ((Polynomial.divByMonic_eq_zero_iff d.property).mp hy).le).trans_le
            d.property.degree_mul.ge

theorem qs_isUnit_one_add_of_polynomialPart_eq_zero
    {R : Type*} [CommRing R] [Nontrivial R]
    (z : Localization (qsMonicSubmonoid R))
    (hz : qsPolynomialPart R z = 0) : IsUnit (1 + z) := by
  induction z using Localization.induction_on with
  | _ z =>
    obtain ⟨a, b⟩ := z
    change a /ₘ (b : Polynomial R) = 0 at hz
    have hdeg : a.degree < (b : Polynomial R).degree :=
      (Polynomial.divByMonic_eq_zero_iff b.property).mp hz
    let s : qsMonicSubmonoid R :=
      ⟨(b : Polynomial R) + a, b.property.add_of_left hdeg⟩
    refine isUnit_iff_exists_inv.mpr
      ⟨Localization.mk (b : Polynomial R) s, ?_⟩
    calc
      (1 + Localization.mk a b) * Localization.mk (b : Polynomial R) s =
          (Localization.mk (b : Polynomial R) b + Localization.mk a b) *
            Localization.mk (b : Polynomial R) s := by
        rw [Localization.mk_self]
      _ = Localization.mk ((b : Polynomial R) + a) b *
            Localization.mk (b : Polynomial R) s := by
        rw [Localization.add_mk_self]
      _ = Localization.mk (((b : Polynomial R) + a) * b) (b * s) := by
        rw [Localization.mk_mul]
      _ = Localization.mk (↑(b * s) : Polynomial R) (b * s) := by
        congr 1
        simp only [Submonoid.coe_mul]
        change ((b : Polynomial R) + a) * b =
          (b : Polynomial R) * ((b : Polynomial R) + a)
        exact mul_comm _ _
      _ = 1 := Localization.mk_self (b * s)

theorem qsPolynomialPart_C_mul
    {R : Type*} [CommRing R] [Nontrivial R]
    (r : R) (z : Localization (qsMonicSubmonoid R)) :
    qsPolynomialPart R
        (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R))
          (Polynomial.C r) * z) =
      r • qsPolynomialPart R z := by
  change qsPolynomialPart R (algebraMap R
    (Localization (qsMonicSubmonoid R)) r * z) = _
  rw [← Algebra.smul_def, map_smul]

theorem qsPolynomialPart_mul_of_constant_parts
    {R : Type*} [CommRing R] [Nontrivial R]
    {x y : Localization (qsMonicSubmonoid R)} {r s : R}
    (hx : qsPolynomialPart R x = Polynomial.C r)
    (hy : qsPolynomialPart R y = Polynomial.C s) :
    qsPolynomialPart R (x * y) = Polynomial.C (r * s) := by
  let alg : Polynomial R →+* Localization (qsMonicSubmonoid R) :=
    algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R))
  let x₀ := x - alg (Polynomial.C r)
  let y₀ := y - alg (Polynomial.C s)
  have halg (p : Polynomial R) : qsPolynomialPart R (alg p) = p := by
    exact qsPolynomialPart_algebraMap p
  have hx₀ : qsPolynomialPart R x₀ = 0 := by
    rw [show qsPolynomialPart R x₀ = qsPolynomialPart R x -
        qsPolynomialPart R (alg (Polynomial.C r)) by simp [x₀], hx, halg,
      sub_self]
  have hy₀ : qsPolynomialPart R y₀ = 0 := by
    rw [show qsPolynomialPart R y₀ = qsPolynomialPart R y -
        qsPolynomialPart R (alg (Polynomial.C s)) by simp [y₀], hy, halg,
      sub_self]
  have hxy₀ : qsPolynomialPart R (x₀ * y₀) = 0 :=
    qsPolynomialPart_mul_eq_zero hx₀ hy₀
  have hxsplit : alg (Polynomial.C r) + x₀ = x := by
    dsimp only [x₀]
    abel
  have hysplit : alg (Polynomial.C s) + y₀ = y := by
    dsimp only [y₀]
    abel
  calc
    qsPolynomialPart R (x * y) = qsPolynomialPart R
        ((alg (Polynomial.C r) + x₀) * (alg (Polynomial.C s) + y₀)) := by
      rw [hxsplit, hysplit]
    _ = qsPolynomialPart R
        (alg (Polynomial.C r) * alg (Polynomial.C s) +
          alg (Polynomial.C r) * y₀ + x₀ * alg (Polynomial.C s) + x₀ * y₀) := by
      congr 1
      ring
    _ = Polynomial.C (r * s) + r • qsPolynomialPart R y₀ +
        s • qsPolynomialPart R x₀ + qsPolynomialPart R (x₀ * y₀) := by
      simp only [map_add]
      rw [← map_mul, ← Polynomial.C_mul, qsPolynomialPart_algebraMap,
        qsPolynomialPart_C_mul, mul_comm x₀, qsPolynomialPart_C_mul]
    _ = Polynomial.C (r * s) := by rw [hx₀, hy₀, hxy₀]; simp

theorem qsPolynomialPart_prod_of_constant_parts
    {R : Type*} [CommRing R] [Nontrivial R]
    {α : Type*} (t : Finset α)
    (f : α → Localization (qsMonicSubmonoid R)) (g : α → R)
    (h : ∀ i ∈ t, qsPolynomialPart R (f i) = Polynomial.C (g i)) :
    qsPolynomialPart R (∏ i ∈ t, f i) = Polynomial.C (∏ i ∈ t, g i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using qsPolynomialPart_algebraMap (R := R) (1 : Polynomial R)
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      apply qsPolynomialPart_mul_of_constant_parts
      · exact h a (Finset.mem_insert_self a t)
      · exact ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)

theorem qsPolynomialPart_det_of_constant_parts
    {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (Localization (qsMonicSubmonoid R)))
    (M : Matrix ι ι R)
    (h : ∀ i j, qsPolynomialPart R (H i j) = Polynomial.C (M i j)) :
    qsPolynomialPart R H.det = Polynomial.C M.det := by
  rw [Matrix.det_apply, map_sum, Matrix.det_apply,
    map_sum (Polynomial.C : R →+* Polynomial R)]
  apply Finset.sum_congr rfl
  intro σ _
  have hprod : qsPolynomialPart R (∏ i, H (σ i) i) =
      Polynomial.C (∏ i, M (σ i) i) :=
    qsPolynomialPart_prod_of_constant_parts Finset.univ
      (fun i ↦ H (σ i) i) (fun i ↦ M (σ i) i) fun i _ ↦ h _ _
  obtain hs | hs := Int.units_eq_one_or (Equiv.Perm.sign σ)
  · rw [hs, one_smul, one_smul, hprod]
  · rw [hs, Units.neg_smul, one_smul, Units.neg_smul, one_smul,
      map_neg, hprod, map_neg]

theorem qs_isUnit_det_of_matrixPolynomialPart_eq_one
    {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (Localization (qsMonicSubmonoid R)))
    (hH : ∀ i j, qsPolynomialPart R (H i j) =
      (1 : Matrix ι ι (Polynomial R)) i j) : IsUnit H.det := by
  have hentry : ∀ i j, qsPolynomialPart R (H i j) =
      Polynomial.C ((1 : Matrix ι ι R) i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa using hH i i
    · simpa [Matrix.one_apply, hij] using hH i j
  have hdet : qsPolynomialPart R H.det = 1 := by
    calc
      qsPolynomialPart R H.det = Polynomial.C (1 : Matrix ι ι R).det :=
        qsPolynomialPart_det_of_constant_parts H 1 hentry
      _ = 1 := by rw [Matrix.det_one, map_one]
  have hproper : qsPolynomialPart R (H.det - 1) = 0 := by
    have hone : qsPolynomialPart R
        (1 : Localization (qsMonicSubmonoid R)) = 1 := by
      simpa using qsPolynomialPart_algebraMap (R := R) (1 : Polynomial R)
    rw [map_sub, hdet, hone, sub_self]
  have hu := qs_isUnit_one_add_of_polynomialPart_eq_zero (H.det - 1) hproper
  have heq : 1 + (H.det - 1) = H.det := by ring
  rw [heq] at hu
  exact hu

end QuillenSuslin
