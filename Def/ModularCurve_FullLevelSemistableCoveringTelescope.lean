module
public import Def.ModularCurve_FullLevelSemistableCovering
public import Instance.ModularCurve_FullLevelSemistableCoveringTelescope
public import Abbrev.ModularCurve_FullLevelSemistableCoveringTelescope
set_option autoImplicit false


public section

noncomputable section

namespace ModularCurve.FullLevel.SemistableCovering

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
variable (𝒞 : SemistableCovering q M' A W)

def sumFbar : CuspidalType.ProjLine q ⊕ ↥W → Type
  | .inl ℓ => 𝒞.FIg ℓ
  | .inr s => 𝒞.FSS s

def sumChart : ∀ j, ComponentChart A (fieldBar q M') (𝒞.sumFbar j)
  | .inl ℓ => 𝒞.CIg ℓ
  | .inr s => 𝒞.CSS s

def sumNode : ∀ j, CuspidalType.ProjLine q × ↥W → Place (ResidueField A) (𝒞.sumFbar j)
  | .inl ℓ => fun p => 𝒞.xs ℓ p.2
  | .inr s => fun p => 𝒞.xt p.1 s

def eIdx (𝒞 : SemistableCovering q M' A W) : CuspidalType.ProjLine q ⊕ ↥W ≃ Fin 𝒞.teleN := Finite.equivFin _

def eEdge (𝒞 : SemistableCovering q M' A W) : CuspidalType.ProjLine q × ↥W ≃ Fin 𝒞.teleM := Finite.equivFin _

def eIg (𝒞 : SemistableCovering q M' A W) (ℓ : CuspidalType.ProjLine q) : Fin 𝒞.teleN := 𝒞.eIdx (Sum.inl ℓ)

def eSS (𝒞 : SemistableCovering q M' A W) (s : ↥W) : Fin 𝒞.teleN := 𝒞.eIdx (Sum.inr s)

abbrev eAn (𝒞 : SemistableCovering q M' A W) : CuspidalType.ProjLine q × ↥W ≃ Fin 𝒞.teleM := 𝒞.eEdge

def teleFbar (i : Fin 𝒞.teleN) : Type := 𝒞.sumFbar (𝒞.eIdx.symm i)

def teleChart (i : Fin 𝒞.teleN) : ComponentChart A (fieldBar q M') (𝒞.teleFbar i) := 𝒞.sumChart (𝒞.eIdx.symm i)

def teleAn (e : Fin 𝒞.teleM) : Annulus A (fieldBar q M') := 𝒞.An (𝒞.eEdge.symm e).1 (𝒞.eEdge.symm e).2

def teleAn' (e : Fin 𝒞.teleM) : Annulus A (fieldBar q M') := 𝒞.An' (𝒞.eEdge.symm e).1 (𝒞.eEdge.symm e).2

def teleWidth (π : A) (e : Fin 𝒞.teleM) : ℕ := by
def teleSrc (e : Fin 𝒞.teleM) : Fin 𝒞.teleN := 𝒞.eIdx (Sum.inl (𝒞.eEdge.symm e).1)

def teleTgt (e : Fin 𝒞.teleM) : Fin 𝒞.teleN := 𝒞.eIdx (Sum.inr (𝒞.eEdge.symm e).2)

def teleXs (e : Fin 𝒞.teleM) : Place (ResidueField A) (𝒞.teleFbar (𝒞.teleSrc e)) :=
  𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl (𝒞.eEdge.symm e).1))) (𝒞.eEdge.symm e)

def teleXt (e : Fin 𝒞.teleM) : Place (ResidueField A) (𝒞.teleFbar (𝒞.teleTgt e)) :=
  𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr (𝒞.eEdge.symm e).2))) (𝒞.eEdge.symm e)

end ModularCurve.FullLevel.SemistableCovering

end
