import Lemma.ModularCurve.ComponentGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Defs
import Structure.CerednikDrinfeld_Ribbon

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*}


theorem mem_ribbonKernel [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {x : E → ℤ} : x ∈ ribbonKernel D ↔ ∀ i, jointDelta D i x = 0 := by
  simp [ribbonKernel, Submodule.mem_iInf, LinearMap.mem_ker]

theorem degreeOn_pushforward [Fintype E] [Fintype V] [DecidableEq V] (f : E → V)
    (x : E → ℤ) : degreeOn V (pushforward f x) = degreeOn E x := by
  classical
  simp only [degreeOn_apply, pushforward, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

theorem ribbonKernel_le_characterLattice [Fintype E] [Fintype V] [DecidableEq V]
    (D : DegeneracyData E V) : ribbonKernel D ≤ characterLattice E := by
  intro x hx
  rw [mem_ribbonKernel] at hx
  have h0 : pushforward D.a x = 0 := by
    simpa [jointDelta] using hx 0
  have hdeg : degreeOn E x = 0 := by
    rw [← degreeOn_pushforward D.a x, h0, map_zero]
  simpa [characterLattice, LinearMap.mem_ker] using hdeg

def ribbonGram [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    ribbonKernel D →ₗ[ℤ] Module.Dual ℤ (ribbonKernel D) :=
  (widthPairing (fun e => (D.w e : ℕ))).domRestrict₁₂ (ribbonKernel D) (ribbonKernel D)

@[simp] theorem ribbonGram_apply [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (x y : ribbonKernel D) :
    ribbonGram D x y = ∑ e : E, (D.w e : ℤ) * (x.1 e * y.1 e) :=
  rfl

abbrev ribbonComponentGroup [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) :=
  Module.Dual ℤ ↥(ribbonKernel D) ⧸ LinearMap.range (ribbonGram D)

abbrev ribbonComponentGroupProj [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) :
    Module.Dual ℤ ↥(ribbonKernel D) →ₗ[ℤ] ribbonComponentGroup D :=
  (LinearMap.range (ribbonGram D)).mkQ

theorem ribbonGram_range_map_dualMap_le [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (A B : ribbonKernel D →ₗ[ℤ] ribbonKernel D)
    (hadj : ∀ x y : ribbonKernel D, ribbonGram D (A x) y = ribbonGram D x (B y)) :
    (LinearMap.range (ribbonGram D)).map B.dualMap ≤ LinearMap.range (ribbonGram D) := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hf
  refine LinearMap.mem_range.mpr ⟨A x, ?_⟩
  ext y
  rw [LinearMap.dualMap_apply]
  exact hadj x y

def ribbonComponentGroupMap [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (A B : ribbonKernel D →ₗ[ℤ] ribbonKernel D)
    (hadj : ∀ x y : ribbonKernel D, ribbonGram D (A x) y = ribbonGram D x (B y)) :
    ribbonComponentGroup D →ₗ[ℤ] ribbonComponentGroup D :=
  (LinearMap.range (ribbonGram D)).mapQ (LinearMap.range (ribbonGram D)) B.dualMap
    (fun _ hf => ribbonGram_range_map_dualMap_le D A B hadj (Submodule.mem_map_of_mem hf))


theorem ribbonKernel_stable [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ∀ x ∈ ribbonKernel D, (H.T ℓ).mulVecLin x ∈ ribbonKernel D := by
  intro x hx
  rw [mem_ribbonKernel] at hx ⊢
  exact H.kernel_stable ℓ x hx

def heckeKernelMap [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ribbonKernel D →ₗ[ℤ] ribbonKernel D :=
  ((H.T ℓ).mulVecLin).restrict (ribbonKernel_stable H ℓ)

variable {E₁ V₁ E₂ V₂ : Type*}


end CerednikDrinfeld
