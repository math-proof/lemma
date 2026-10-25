import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Exact
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset

section CharacterLattice
variable {ι : Type*} [Fintype ι]

def degreeOn (ι : Type*) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] ℤ :=
  ∑ x : ι, LinearMap.proj x


def characterLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (degreeOn ι)

end CharacterLattice

section Pairing
variable {ι : Type*} [Fintype ι]

def widthPairing (e : ι → ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun D D' => ∑ x : ι, (e x : ℤ) * (D x * D' x))
    (fun D₁ D₂ D' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun D D'₁ D'₂ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)


def gramMap (e : ι → ℕ) :
    characterLattice ι →ₗ[ℤ] Module.Dual ℤ (characterLattice ι) :=
  (widthPairing e).domRestrict₁₂ (characterLattice ι) (characterLattice ι)

end Pairing

end ModularCurve

end
