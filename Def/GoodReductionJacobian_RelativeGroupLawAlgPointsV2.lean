module
public import Mathlib
public import Def.GoodReductionJacobian_RelativeGroupLawKernel
public import Def.AlgebraicGeometry_RelativeGroupLawEndDegree
public import Instance.GoodReductionJacobian_RelativeGroupLawAlgPointsV2
set_option autoImplicit false


public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Scheme

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

def AlgPoints (L : RelativeGroupLaw R f) (_hc : L.IsCommutative) (T : Type) [CommRing T]
    [Algebra R T] : Type :=
  Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f)

namespace AlgPoints

variable {L : RelativeGroupLaw R f} {hc : L.IsCommutative}
variable {T : Type} [CommRing T] [Algebra R T]

def ofPoint (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    L.AlgPoints hc T := Additive.ofMul x

def toPoint (x : L.AlgPoints hc T) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f := Additive.toMul x

def equivPoint : L.AlgPoints hc T ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f where
  toFun := toPoint
  invFun := ofPoint
  left_inv _ := rfl
  right_inv _ := rfl

def torsionByEquiv (n : ℕ) :
    Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ) ≃
      L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n where
  toFun x := ⟨toPoint (x : L.AlgPoints hc T), (mem_torsionBy_iff n _).1 x.2⟩
  invFun y := ⟨ofPoint y.1, (mem_torsionBy_iff n _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Map

variable {T' : Type} [CommRing T'] [Algebra R T'] {T'' : Type} [CommRing T''] [Algebra R T'']

def mapPoint (a : T →ₐ[R] T')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T'))) f :=
  GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom a.toRingHom))
    (specMap_comp_algebraMap a) x

def map (a : T →ₐ[R] T') : L.AlgPoints hc T →+ L.AlgPoints hc T' :=
  AddMonoidHom.mk' (fun x => ofPoint (mapPoint a (toPoint x))) fun x y => by
    apply toPoint_injective
    change mapPoint a (toPoint (x + y)) = L.mul _ (mapPoint a (toPoint x)) (mapPoint a (toPoint y))
    rw [toPoint_add]
    exact mapPoint_mul a _ _

end Map

end AlgPoints

end RelativeGroupLaw
end GoodReductionJacobian

end
