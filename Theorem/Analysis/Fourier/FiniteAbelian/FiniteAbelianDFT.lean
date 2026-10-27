/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Star.BigOperators
import Def.Analysis.Fourier.FiniteAbelian.FiniteAbelianDFT
open scoped BigOperators


namespace Fourier.FiniteAbelianDFTWanted

theorem dft_orthogonality {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (x y : G) :
    (∑ ψ : AddChar G ℂ, star (ψ x) * ψ y) =
      if y = x then (Fintype.card G : ℂ) else 0 := by
  classical
  calc
    (∑ ψ : AddChar G ℂ, star (ψ x) * ψ y) = ∑ ψ : AddChar G ℂ, ψ (-x + y) := by
      apply Finset.sum_congr rfl
      intro ψ _
      rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj, starRingEnd_apply]
    _ = if -x + y = 0 then (Fintype.card G : ℂ) else 0 :=
      AddChar.sum_apply_eq_ite (-x + y)
    _ = if y = x then (Fintype.card G : ℂ) else 0 := by
      simp only [neg_add_eq_zero, eq_comm]

theorem dft_inversion_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (x : G) :
    (∑ ψ : AddChar G ℂ, star (ψ x) * dftFun f ψ) = (Fintype.card G : ℂ) * f x := by
  classical
  calc
    (∑ ψ : AddChar G ℂ, star (ψ x) * dftFun f ψ) =
        ∑ ψ : AddChar G ℂ, ∑ y : G, star (ψ x) * (ψ y * f y) := by
      simp only [dftFun, Finset.mul_sum]
    _ = ∑ y : G, ∑ ψ : AddChar G ℂ, star (ψ x) * (ψ y * f y) := by
      rw [Finset.sum_comm]
    _ = ∑ y : G, (∑ ψ : AddChar G ℂ, star (ψ x) * ψ y) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = ∑ y : G, (if y = x then (Fintype.card G : ℂ) else 0) * f y := by
      simp_rw [dft_orthogonality]
    _ = (Fintype.card G : ℂ) * f x := by
      simp

theorem dft_star_dftFun {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (ψ : AddChar G ℂ) :
    (∑ x : G, star (f x) * star (ψ x)) = star (dftFun f ψ) := by
  rw [dftFun, star_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [star_mul']
  exact mul_comm _ _

/--
Fourier inversion on a finite abelian group.

Sources: `undergrad.yaml`, section "Fourier transform", entry "discrete
Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on
Finite Groups and Applications, Ch. 2, Fourier inversion theorem.

Proves `Wanted` entry `dft_inversion`.

Proof: expand the transform and collapse the inner sum with the orthogonality of characters
from Mathlib's Pontryagin duality. This is the Fourier inversion formula (4.4) of K. Conrad,
Characters of finite abelian groups, Section 4,
https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, up to reindexing `ψ ↦ ψ⁻¹`
(Conrad conjugates the character in the transform rather than in the inversion sum).
-/
public theorem dft_inversion {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (x : G) :
    f x = ((Fintype.card G : ℂ))⁻¹ *
      ∑ ψ : AddChar G ℂ, star (ψ x) * dftFun f ψ := by
  rw [dft_inversion_sum]
  exact (inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (f x)).symm

/--
Plancherel formula on a finite abelian group.

Sources: `undergrad.yaml`, section "Fourier transform", entry "discrete
Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on
Finite Groups and Applications, Ch. 2, Plancherel formula.

Proves `Wanted` entry `dft_plancherel`.

Proof: apply Fourier inversion to `g`, exchange the finite sums, and identify the conjugated
inner sum with `star (dftFun f ψ)`. Conrad (Section 4, cited above) proves the same identity by
checking it on characters.
-/
public theorem dft_plancherel {G : Type*} [AddCommGroup G] [Fintype G]
    (f g : G → ℂ) :
    (∑ x : G, star (f x) * g x) = ((Fintype.card G : ℂ))⁻¹ *
      ∑ ψ : AddChar G ℂ, star (dftFun f ψ) * dftFun g ψ := by
  classical
  calc
    (∑ x : G, star (f x) * g x) =
        ∑ x : G, star (f x) * ((Fintype.card G : ℂ)⁻¹ *
          ∑ ψ : AddChar G ℂ, star (ψ x) * dftFun g ψ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [dft_inversion g x]
    _ = ∑ x : G, (Fintype.card G : ℂ)⁻¹ *
        ∑ ψ : AddChar G ℂ, star (f x) * (star (ψ x) * dftFun g ψ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← mul_assoc, mul_comm (star (f x)), mul_assoc, Finset.mul_sum]
    _ = (Fintype.card G : ℂ)⁻¹ *
        ∑ x : G, ∑ ψ : AddChar G ℂ,
          star (f x) * (star (ψ x) * dftFun g ψ) := by
      rw [Finset.mul_sum]
    _ = (Fintype.card G : ℂ)⁻¹ *
        ∑ ψ : AddChar G ℂ, ∑ x : G,
          star (f x) * (star (ψ x) * dftFun g ψ) := by
      rw [Finset.sum_comm]
    _ = (Fintype.card G : ℂ)⁻¹ *
        ∑ ψ : AddChar G ℂ, (∑ x : G, star (f x) * star (ψ x)) * dftFun g ψ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = (Fintype.card G : ℂ)⁻¹ *
        ∑ ψ : AddChar G ℂ, star (dftFun f ψ) * dftFun g ψ := by
      simp_rw [dft_star_dftFun]

/--
Translation of the input modulates the Fourier transform by the character.

Sources: `undergrad.yaml`, section "Fourier transform", entry "discrete
Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on
Finite Groups and Applications, Ch. 2 (translation and modulation).

Proves `Wanted` entry `dftFun_translate`.

Proof: reindex the finite sum by `x ↦ x + t` and use character additivity.
-/
public theorem dftFun_translate {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (t : G) (ψ : AddChar G ℂ) :
    dftFun (fun x => f (x - t)) ψ = ψ t * dftFun f ψ := by
  classical
  calc
    dftFun (fun x => f (x - t)) ψ = ∑ x : G, ψ x * f (x - t) := rfl
    _ = ∑ x : G, ψ (x + t) * f x := by
      symm
      apply Fintype.sum_equiv (Equiv.addRight t)
      intro x
      simp
    _ = ∑ x : G, (ψ x * ψ t) * f x := by
      simp_rw [AddChar.map_add_eq_mul]
    _ = ψ t * ∑ x : G, ψ x * f x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ψ t * dftFun f ψ := rfl

end Fourier.FiniteAbelianDFTWanted
