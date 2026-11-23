import Mathlib
import Def.AlgebraicGeometry_RelativeGroupLaw
import Def.GoodReductionJacobian_RelativeGroupLawKernel
import Theorem.Scheme.NeronModelEndomorphismExtension
import Instance.AlgebraicGeometry_RelativeGroupLawEndDegree
import Abbrev.AlgebraicGeometry_RelativeGroupLawEndDegree

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Scheme

namespace NeronModelInfra

variable {B X : Scheme.{u}} {f : X ⟶ B}

def schemeHomOverNpow (β : SchemeHomOver f f) : ℕ → SchemeHomOver f f
  | 0 => schemeHomOverId f
  | i + 1 => schemeHomOverComp (schemeHomOverNpow β i) β

end NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section General

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

@[reducible]
def pointCommGroup (G : RelativeGroupLaw R f) (hc : G.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (SchemeHomOver t f) :=
  { G.pointGroup t with mul_comm := fun x y => hc t x y }

def endAeval (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (β : SchemeHomOver f f)
    (p : Polynomial ℤ) : SchemeHomOver f f :=
  letI := G.pointCommGroup hc f
  ∏ i ∈ Finset.range (p.natDegree + 1), NeronModelInfra.schemeHomOverNpow β i ^ p.coeff i

end General

section Field

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

def endDegree (G : RelativeGroupLaw K f) (β : SchemeHomOver f f) : ℕ := by
end Field

end RelativeGroupLaw
end GoodReductionJacobian

end
