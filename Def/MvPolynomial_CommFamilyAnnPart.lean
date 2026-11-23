module

public import Mathlib
public import Instance.Module_CommFamilyAnnPart
public import Structure.Module_CommFamilyAnnPart

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace Module.End

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] (σ : Type*)


variable {K V σ}

namespace CommFamily

variable (F : CommFamily K V σ)

def adjoin : Subalgebra K (Module.End K V) := Algebra.adjoin K (Set.range F.T)

def gen (a : σ) : F.adjoin := ⟨F.T a, Algebra.subset_adjoin (Set.mem_range_self a)⟩

noncomputable def eval : MvPolynomial σ K →ₐ[K] Module.End K V :=
  F.adjoin.val.comp (MvPolynomial.aeval F.gen)

noncomputable def annPart (p : ℕ) [Fact p.Prime] [CharP K p] (θ : σ → K) : Submodule K V :=
  ⨅ (Q : MvPolynomial σ (ZMod p))
    (_ : MvPolynomial.aeval θ (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q) = 0),
    LinearMap.ker (F.eval (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q))

end CommFamily

end Module.End

end
