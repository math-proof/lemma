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
import Def.Algebra.Module.QuillenSuslin.Part8
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qsHorrocksMap_apply
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} [Fintype ι]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (F : Matrix κ ι (Polynomial R)) :
    qsHorrocksMap R A F = qsMatrixPolynomialPart R
      (F.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))) * A) :=
  rfl

theorem qs_exists_monic_matrix_multiple
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} [Finite ι] [Finite κ]
    (B : Matrix ι κ (Localization (qsMonicSubmonoid R))) :
    ∃ h : Polynomial R, h.Monic ∧
      ∃ B₀ : Matrix ι κ (Polynomial R),
        B₀.map (algebraMap (Polynomial R)
          (Localization (qsMonicSubmonoid R))) =
          (algebraMap (Polynomial R)
            (Localization (qsMonicSubmonoid R)) h) • B := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  let f : ι × κ → Localization (qsMonicSubmonoid R) :=
    fun z ↦ B z.1 z.2
  obtain ⟨h, hh⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (qsMonicSubmonoid R) f
  choose b₀ hb₀ using hh
  refine ⟨h, h.property, fun i j ↦ b₀ (i, j), ?_⟩
  apply Matrix.ext
  intro i j
  have hij := hb₀ (i, j)
  rw [Algebra.smul_def] at hij
  exact hij

theorem qs_horrocks_multiple_mem_range
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} [Fintype ι] [Finite κ] [DecidableEq κ]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
    (hBA : B * A = 1)
    (h : Polynomial R) (B₀ : Matrix κ ι (Polynomial R))
    (hB₀ : B₀.map (algebraMap (Polynomial R)
      (Localization (qsMonicSubmonoid R))) =
      (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R)) h) • B)
    (G : Matrix κ κ (Polynomial R)) :
    h • G ∈ LinearMap.range (qsHorrocksMap R A) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let Q := Localization (qsMonicSubmonoid R)
  let alg : Polynomial R →+* Q := algebraMap (Polynomial R) Q
  refine ⟨G * B₀, ?_⟩
  rw [qsHorrocksMap_apply]
  have hsmul : (h • G).map alg = (alg h) • G.map alg := by
    apply Matrix.ext
    intro i j
    change alg (h * G i j) = alg h * alg (G i j)
    exact map_mul alg h (G i j)
  calc
    qsMatrixPolynomialPart R ((G * B₀).map alg * A) =
        qsMatrixPolynomialPart R ((G.map alg * B₀.map alg) * A) := by
      rw [Matrix.map_mul]
    _ = qsMatrixPolynomialPart R
        ((G.map alg * ((alg h) • B)) * A) := by rw [hB₀]
    _ = qsMatrixPolynomialPart R
        ((alg h) • (G.map alg * (B * A))) := by
      congr 1
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = qsMatrixPolynomialPart R ((alg h) • G.map alg) := by
      rw [hBA, Matrix.mul_one]
    _ = qsMatrixPolynomialPart R ((h • G).map alg) := by rw [hsmul]
    _ = h • G := qsMatrixPolynomialPart_algebraMap (h • G)

theorem qs_matrix_mem_maximal_smul_of_map_eq_zero
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Matrix ι κ (Polynomial R))
    (hP : P.map (Polynomial.mapRingHom (IsLocalRing.residue R)) = 0) :
    P ∈ IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (Matrix ι κ (Polynomial R))) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  rw [Matrix.matrix_eq_sum_single P]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ?_
  have hij := congrFun (congrFun hP i) j
  change (P i j).map (IsLocalRing.residue R) = 0 at hij
  have hp : P i j ∈ IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (Polynomial R)) := by
    rw [Ideal.smul_top_eq_map]
    change P i j ∈ (IsLocalRing.maximalIdeal R).map Polynomial.C
    rw [← IsLocalRing.ker_residue,
      ← Polynomial.ker_mapRingHom, RingHom.mem_ker]
    exact hij
  let f : Polynomial R →ₗ[R] Matrix ι κ (Polynomial R) :=
    Matrix.singleLinearMap R i j
  have hmap : Matrix.single i j (P i j) ∈
      Submodule.map f (IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R (Polynomial R))) := ⟨P i j, hp, rfl⟩
  rw [Submodule.map_smul''] at hmap
  exact (Submodule.smul_mono le_rfl le_top) hmap

end QuillenSuslin
