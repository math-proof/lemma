import Instance.CuspForm_TWLevelHeckeModule
import Instance.CuspForm_TWLevelHeckeRing

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups


namespace CuspForm.TWLevel

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ) [NeZero N] [NeZero r] [∀ i, NeZero (qv i)]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪)
  (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)

omit [NeZero r] in

def opML : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg →ₐ[𝒪] Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) :=
  Algebra.lsmul 𝒪 𝒪 (ML N r qv S 𝒪 H θ α hc)

omit [NeZero r] in


def heckeRingGens : Set (Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      T = opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL))} ∪
  {D | ∃ u ∈ HR N r qv, D = diaML N r qv S 𝒪 H θ α hc hdc u}


def heckeSubalgebra : Subalgebra 𝒪 (Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) :=
  Algebra.adjoin 𝒪 (heckeRingGens N r qv S 𝒪 H θ α hc hdc)

def HeckeRing : Type := ↥(heckeSubalgebra N r qv S 𝒪 H θ α hc hdc)

namespace HeckeRing

def act : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) :=
  (heckeSubalgebra N r qv S 𝒪 H θ α hc hdc).val


def T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv) :
    HeckeRing N r qv S 𝒪 H θ α hc hdc :=
  ⟨opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL)),
    Algebra.subset_adjoin (Or.inl ⟨ℓ, hℓ, hℓS, hℓL, rfl⟩)⟩


def diamond (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) : HeckeRing N r qv S 𝒪 H θ α hc hdc :=
  ⟨diaML N r qv S 𝒪 H θ α hc hdc u, Algebra.subset_adjoin (Or.inr ⟨u, hu, rfl⟩)⟩

end HeckeRing

end CuspForm.TWLevel

end
