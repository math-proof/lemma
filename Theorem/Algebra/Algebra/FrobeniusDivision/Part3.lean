import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Algebra.Algebra.FrobeniusDivision.Part2
/-!
# Frobenius theorem on real division algebras

Proves the classification of finite-dimensional associative division ℝ-algebras.
-/


namespace FrobeniusDivision

theorem quatHom_injective {A : Type*} [DivisionRing A] [Algebra ℝ A]
    (f : Quaternion ℝ →ₐ[ℝ] A) : Function.Injective f :=
  RingHom.injective f.toRingHom

-- Helper 20: expansion of `quatHom` on components.
theorem quatHom_mk {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {i j : A} (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) (a b c d : ℝ) :
    quatHom hi hj hanti (QuaternionAlgebra.mk a b c d)
      = algebraMap ℝ A a + b • i + c • j + d • (i * j) := by
  change ((quatBasis hi hj hanti).liftHom) _ = _
  rw [QuaternionAlgebra.Basis.liftHom_apply]
  rfl

-- Helper 21: product of two anticommuting elements commutes.
theorem comm_of_anticomm_anticomm {A : Type*} [DivisionRing A]
    {i j a : A} (ha : i * a = -(a * i)) (hji : j * i = -(i * j)) :
    (a * j) * i = i * (a * j) := by
  have e1 : (a * j) * i = -(a * (i * j)) := by
    rw [mul_assoc, hji, mul_neg]
  have e2 : i * (a * j) = -(a * (i * j)) := by
    rw [← mul_assoc, ha, neg_mul, ← mul_assoc]
  rw [e1, e2]

-- Helper 22: a non-`ℝ` element exists unless the dimension is one.
theorem exists_nonreal {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (h1 : Module.finrank ℝ A ≠ 1) :
    ∃ x : A, ∀ r : ℝ, algebraMap ℝ A r ≠ x := by
  by_contra hcon
  have hall : ∀ z : A, ∃ r : ℝ, algebraMap ℝ A r = z := by
    intro z
    by_contra hz
    apply hcon
    exact ⟨z, fun r hr => hz ⟨r, hr⟩⟩
  have hbij : Function.Bijective (Algebra.ofId ℝ A) := by
    refine ⟨algMap_injective, ?_⟩
    intro z
    exact hall z
  have e := AlgEquiv.ofBijective (Algebra.ofId ℝ A) hbij
  have hfin := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_self] at hfin
  exact h1 hfin.symm

-- Helper 23: the quaternion embedding is surjective. Every `x` decomposes as
-- `u + w * j` with `u`, `w` commuting with `i` (symmetric/antisymmetric parts
-- under conjugation `x ↦ i * x * i`, halved by the central scalar `(2:ℝ)⁻¹`).
theorem quatHom_surjective {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A]
    {i j : A} (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    Function.Surjective (quatHom hi hj hanti) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hji : j * i = -(i * j) := eq_neg_of_add_eq_zero_right hanti
  intro x
  have h1 : (i * x * i) * i = -(i * x) := by
    rw [mul_assoc (i * x) i i, hi, mul_neg, mul_one]
  have h2' : i * (i * x * i) = -(x * i) := by
    rw [← mul_assoc i (i * x) i, ← mul_assoc i i x, hi, neg_mul, one_mul,
      neg_mul]
  have key : (x - i * x * i) * i = i * (x - i * x * i) := by
    rw [sub_mul, mul_sub, h1, h2', sub_neg_eq_add, sub_neg_eq_add]
    exact add_comm _ _
  have key2 : i * (x + i * x * i) = -((x + i * x * i) * i) := by
    rw [add_mul, mul_add, h2', h1, neg_add, neg_neg]
    exact add_comm _ _
  have hu : ((2 : ℝ)⁻¹ • (x - i * x * i)) * i
      = i * ((2 : ℝ)⁻¹ • (x - i * x * i)) := by
    rw [Algebra.smul_def,
      mul_assoc (algebraMap ℝ A ((2 : ℝ)⁻¹)) (x - i * x * i) i,
      ← mul_assoc i _ _,
      ← (Algebra.commute_algebraMap_left ((2 : ℝ)⁻¹) i).eq,
      mul_assoc (algebraMap ℝ A ((2 : ℝ)⁻¹)) i (x - i * x * i), key]
  obtain ⟨z₁, hz₁⟩ := (AlgHom.mem_range _).mp
    (centralizer_eq_range hi _ hu)
  have ha : i * ((2 : ℝ)⁻¹ • (x + i * x * i))
      = -(((2 : ℝ)⁻¹ • (x + i * x * i)) * i) := by
    have e1 : i * ((2 : ℝ)⁻¹ • (x + i * x * i))
        = algebraMap ℝ A ((2 : ℝ)⁻¹) * (i * (x + i * x * i)) := by
      rw [Algebra.smul_def, ← mul_assoc i _ _,
        ← (Algebra.commute_algebraMap_left ((2 : ℝ)⁻¹) i).eq, mul_assoc]
    have e2 : ((2 : ℝ)⁻¹ • (x + i * x * i)) * i
        = algebraMap ℝ A ((2 : ℝ)⁻¹) * ((x + i * x * i) * i) := by
      rw [Algebra.smul_def, mul_assoc]
    rw [e1, e2, key2, mul_neg]
  have hwcomm : (((2 : ℝ)⁻¹ • (x + i * x * i)) * j) * i
      = i * (((2 : ℝ)⁻¹ • (x + i * x * i)) * j) :=
    comm_of_anticomm_anticomm ha hji
  have hwcomm2 : (-(((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) * i
      = i * (-(((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) := by
    rw [neg_mul, mul_neg, hwcomm]
  obtain ⟨z₂, hz₂⟩ := (AlgHom.mem_range _).mp
    (centralizer_eq_range hi _ hwcomm2)
  have ejj : (-(((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) * j
      = (2 : ℝ)⁻¹ • (x + i * x * i) := by
    have e : ((((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) * j
        = ((2 : ℝ)⁻¹ • (x + i * x * i)) * (j * j) := mul_assoc _ _ _
    rw [neg_mul, e, hj, mul_neg, mul_one, neg_neg]
  have esum : ((2 : ℝ)⁻¹ • (x - i * x * i)) + ((2 : ℝ)⁻¹ • (x + i * x * i))
      = x := by
    have e : (x - i * x * i) + (x + i * x * i) = (2 : ℝ) • x := by
      rw [show (2 : ℝ) = 1 + 1 from one_add_one_eq_two.symm, add_smul,
        one_smul]
      abel
    rw [← smul_add, e, Algebra.smul_def, Algebra.smul_def,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ h2, map_one, one_mul]
  have hrec : x = ((2 : ℝ)⁻¹ • (x - i * x * i))
      + (-(((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) * j := by
    rw [ejj]
    exact esum.symm
  have e1 : complexHom hi z₁ = (2 : ℝ)⁻¹ • (x - i * x * i) := hz₁
  have e2' : complexHom hi z₂ = -(((2 : ℝ)⁻¹ • (x + i * x * i)) * j) := hz₂
  rw [complexHom_apply hi z₁] at e1
  rw [complexHom_apply hi z₂] at e2'
  have ej : (algebraMap ℝ A z₂.re + z₂.im • i) * j
      = z₂.re • j + z₂.im • (i * j) := by
    have e : (algebraMap ℝ A z₂.re + z₂.im • i) * j
        = algebraMap ℝ A z₂.re * j + algebraMap ℝ A z₂.im * (i * j) := by
      rw [add_mul, Algebra.smul_def, mul_assoc]
    rw [e, ← Algebra.smul_def z₂.re j, ← Algebra.smul_def z₂.im (i * j)]
  refine ⟨QuaternionAlgebra.mk z₁.re z₁.im z₂.re z₂.im, ?_⟩
  rw [quatHom_mk, hrec, ← e1, add_assoc, ← ej, ← e2']

set_option linter.dupNamespace false in
/--
If `A` is a finite-dimensional associative unital division algebra over `ℝ` (`DivisionRing A`,
`Algebra ℝ A`, `FiniteDimensional ℝ A`), then `A` is `ℝ`-algebra isomorphic to `ℝ`, `ℂ`, or
`Quaternion ℝ`. Source: G. Frobenius, Ueber lineare Substitutionen und bilineare Formen,
J. reine angew. Math. 84 (1878), 1–63, DOI 10.1515/crelle-1878-18788403; textbook in Jacobson,
Basic Algebra II; Lean states associative unital case via `DivisionRing` excluding octonions
intentionally.

Proves `Wanted` entry `frobenius_real_division_algebra`.
-/
theorem frobenius_real_division_algebra
    {A : Type*} [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A] :
    Nonempty (A ≃ₐ[ℝ] ℝ) ∨ Nonempty (A ≃ₐ[ℝ] ℂ) ∨ Nonempty (A ≃ₐ[ℝ] Quaternion ℝ) := by
  by_cases h1 : Module.finrank ℝ A = 1
  · exact Or.inl (equiv_real_of_finrank_one h1)
  · by_cases h2 : Module.finrank ℝ A = 2
    · obtain ⟨x, hx⟩ := exists_nonreal h1
      obtain ⟨i, hi⟩ := exists_sq_eq_neg_one hx
      exact Or.inr (Or.inl
        (equiv_complex_of_finrank_two (complexHom hi) (complexHom_injective _)
          h2))
    · obtain ⟨x, hx⟩ := exists_nonreal h1
      obtain ⟨i, hi⟩ := exists_sq_eq_neg_one hx
      have hex : ∃ w : A, w ∉ AlgHom.range (complexHom hi) := by
        by_contra hcon
        have hall : ∀ z : A, z ∈ AlgHom.range (complexHom hi) := by
          intro z
          by_contra hz
          apply hcon
          exact ⟨z, hz⟩
        have hsurj : Function.Surjective (complexHom hi) := by
          intro a
          exact (AlgHom.mem_range _).mp (hall a)
        have e := AlgEquiv.ofBijective (complexHom hi)
          ⟨complexHom_injective _, hsurj⟩
        have hfin := e.toLinearEquiv.finrank_eq
        rw [Complex.finrank_real_complex] at hfin
        exact h2 hfin.symm
      obtain ⟨w, hw⟩ := hex
      obtain ⟨j, hj, hanti⟩ := exists_anticommute hi hw
      have hbij : Function.Bijective (quatHom hi hj hanti) :=
        ⟨quatHom_injective _, quatHom_surjective hi hj hanti⟩
      exact Or.inr (Or.inr ⟨(AlgEquiv.ofBijective _ hbij).symm⟩)

end FrobeniusDivision
