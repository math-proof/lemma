import Mathlib
import Lemma.Definitions.Def_LatticeTreeOrbital
import Lemma.Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Lemma.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts

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

def FullLattice.act (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) : FullLattice 𝒪 K :=
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

theorem ext' {d d' : DeligneDatum (K := K) π B} (h : d.line = d'.line) : d = d' := by
  cases d; cases d'; cases h; rfl

end DeligneDatum

abbrev OmegaObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type := DeligneDatum (K := K) π B

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def DeligneDatum.IsPullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) : Prop :=
  ∀ M : FullLattice 𝒪 K, d'.line M = (d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap

variable {B}

noncomputable def lineBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) : Submodule B' (latticeBaseChange 𝒪 K B' M) :=
  Submodule.span B' ((LinearMap.rTensor (↥M.1) f.toLinearMap) '' (N : Set (latticeBaseChange 𝒪 K B M)))

def DeligneDatum.IsBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B') : Prop :=
  ∀ M : FullLattice 𝒪 K, d'.line M = lineBaseChange f M (d.line M)

end Datum

section OmegaNr

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
variable (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)

abbrev OmegaNrObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type :=
  (Onr →ₐ[𝒪] B) × OmegaObj (K := K) π B

noncomputable def frobTwist (n : ℤ) {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : Onr →ₐ[𝒪] B :=
  ψ.comp ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)

def OmegaNr.IsTwistedAct (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (x x' : OmegaNrObj (K := K) π Onr B) : Prop :=
  x'.1 = frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) x.1 ∧
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ x.2 x'.2

end OmegaNr

end FormalOmega
end CerednikDrinfeld
