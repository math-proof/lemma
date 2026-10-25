import Mathlib
import Lemma.LatticeTreeOrbital.Main
import Instance.CerednikDrinfeld_BruhatTitsTree
import Def.CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Abbrev.CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

section Datum

variable (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)


variable {𝒪 K}


namespace DeligneDatum

variable {π}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem ext' {d d' : DeligneDatum (K := K) π B} (h : d.line = d'.line) : d = d' := by
  cases d; cases d'; cases h; rfl

end DeligneDatum

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

noncomputable def frobTwist (n : ℤ) {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : Onr →ₐ[𝒪] B :=
  ψ.comp ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)

def OmegaNr.IsTwistedAct (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (x x' : OmegaNrObj (K := K) π Onr B) : Prop :=
  x'.1 = frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) x.1 ∧
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ x.2 x'.2

end OmegaNr

end FormalOmega
end CerednikDrinfeld
