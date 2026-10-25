import Mathlib
import Structure.LatticeTreeOrbital
import Instance.CerednikDrinfeld_BruhatTitsTree
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

section Datum

variable (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)

abbrev latticeBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] (M : FullLattice 𝒪 K) : Type :=
  B ⊗[𝒪] ↥M.1

variable {𝒪 K}

noncomputable def inclBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1) :
    latticeBaseChange 𝒪 K B M' →ₗ[B] latticeBaseChange 𝒪 K B M :=
  (Submodule.inclusion h).baseChange B

theorem mulVecLinR_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (mulVecLinR (R := 𝒪) g) := by
  intro v w hvw
  have h := congrArg (fun x => Matrix.mulVec ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) x) hvw
  simpa only [mulVecLinR_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] using h

noncomputable def latticeMapEquiv (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : Submodule 𝒪 (Fin 2 → K)) :
    ↥M ≃ₗ[𝒪] ↥(latticeMap g M) :=
  Submodule.equivMapOfInjective (mulVecLinR (R := 𝒪) g) (mulVecLinR_injective g) M

abbrev FullLattice.act (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) : FullLattice 𝒪 K :=
  ⟨latticeMap g M.1, M.2.map g⟩

noncomputable def actBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (M : FullLattice 𝒪 K) : latticeBaseChange 𝒪 K B M ≃ₗ[B] latticeBaseChange 𝒪 K B (FullLattice.act g M) :=
  (latticeMapEquiv g M.1).baseChange 𝒪 B _ _

structure DeligneDatum (B : Type) [CommRing B] [Algebra 𝒪 B] : Type where

  line : ∀ M : FullLattice 𝒪 K, Submodule B (latticeBaseChange 𝒪 K B M)

  invertible : ∀ M : FullLattice 𝒪 K, Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ line M)

  mono : ∀ {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1), (line M').map (inclBaseChange B h) ≤ line M

  homothety : ∀ (c : Kˣ) (M : FullLattice 𝒪 K),
    line (FullLattice.act (scalarGL c) M) = (line M).map (actBaseChange B (scalarGL c) M).toLinearMap

  nondeg : ∀ (𝔭 : Ideal B), 𝔭.IsPrime →
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : B) ⊗ₜ[𝒪] v ∉ line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : B) ⊗ₜ[𝒪] v' ∉ line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')))

namespace DeligneDatum

variable {π}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]


end DeligneDatum


variable (B : Type) [CommRing B] [Algebra 𝒪 B]


variable {B}


end Datum

section OmegaNr

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
variable (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)


end OmegaNr

end FormalOmega
end CerednikDrinfeld
