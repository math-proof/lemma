module

public import Mathlib
public import Theorem.Scheme.RelativeGroupLawKernel
public import Theorem.Scheme.RelativeGroupLawEndDegree
public import Instance.GoodReductionJacobian_RelativeGroupLawAlgPointsV2

public noncomputable section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Scheme

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}


@[simp] public theorem toPoint_ofPoint (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    toPoint (ofPoint x : L.AlgPoints hc T) = x := rfl


@[simp] public theorem ofPoint_toPoint (x : L.AlgPoints hc T) : ofPoint (toPoint x) = x := rfl


def AlgPoints (L : RelativeGroupLaw R f) (_hc : L.IsCommutative) (T : Type) [CommRing T]
    [Algebra R T] : Type :=
  Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f)

def ofPoint (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    L.AlgPoints hc T := Additive.ofMul x

public theorem toPoint_injective : Function.Injective (toPoint : L.AlgPoints hc T → _) :=
  fun _ _ h => h


def toPoint (x : L.AlgPoints hc T) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f := Additive.toMul x

@[simp] theorem toPoint_ofPoint (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    toPoint (ofPoint x : L.AlgPoints hc T) = x := rfl

@[simp] theorem ofPoint_toPoint (x : L.AlgPoints hc T) : ofPoint (toPoint x) = x := rfl

public theorem ofPoint_injective :
    Function.Injective (ofPoint : _ → L.AlgPoints hc T) :=
  fun _ _ h => h


@[ext] public theorem ext {x y : L.AlgPoints hc T} (h : toPoint x = toPoint y) : x = y := h


@[simp] public theorem equivPoint_apply (x : L.AlgPoints hc T) : equivPoint x = toPoint x := rfl


@[simp] public theorem equivPoint_symm_apply
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (equivPoint.symm x : L.AlgPoints hc T) = ofPoint x := rfl


@[ext] theorem ext {x y : L.AlgPoints hc T} (h : toPoint x = toPoint y) : x = y := h

def equivPoint : L.AlgPoints hc T ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f where
  toFun := toPoint
  invFun := ofPoint
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivPoint_apply (x : L.AlgPoints hc T) : equivPoint x = toPoint x := rfl

@[simp] theorem equivPoint_symm_apply
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (equivPoint.symm x : L.AlgPoints hc T) = ofPoint x := rfl

public theorem toPoint_add (x y : L.AlgPoints hc T) :
    toPoint (x + y) = L.mul _ (toPoint x) (toPoint y) := rfl


public theorem toPoint_zero : toPoint (0 : L.AlgPoints hc T) = L.one _ := rfl


public theorem toPoint_neg (x : L.AlgPoints hc T) : toPoint (-x) = L.inv _ (toPoint x) := rfl


public theorem ofPoint_mul (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (ofPoint (L.mul _ x y) : L.AlgPoints hc T) = ofPoint x + ofPoint y := rfl


public theorem ofPoint_one : (ofPoint (L.one _) : L.AlgPoints hc T) = 0 := rfl


public theorem ofPoint_inv (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (ofPoint (L.inv _ x) : L.AlgPoints hc T) = -ofPoint x := rfl


public theorem toPoint_nsmul (n : ℕ) (x : L.AlgPoints hc T) :
    toPoint (n • x) = L.nsmul _ n (toPoint x) := by
  induction n with
  | zero => rw [zero_nsmul, nsmul_zero]; rfl
  | succ n ih => rw [succ_nsmul, toPoint_add, ih, nsmul_succ]


public theorem ofPoint_nsmul (n : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (ofPoint (L.nsmul _ n x) : L.AlgPoints hc T) = n • ofPoint x :=
  toPoint_injective (by rw [toPoint_nsmul]; rfl)


public theorem toPoint_natCast_zsmul (n : ℕ) (x : L.AlgPoints hc T) :
    toPoint ((n : ℤ) • x) = L.nsmul _ n (toPoint x) := by
  rw [natCast_zsmul, toPoint_nsmul]


public theorem nsmul_eq_zero_iff (n : ℕ) (x : L.AlgPoints hc T) :
    n • x = 0 ↔ L.IsTorsionPoint _ n (toPoint x) := by
  rw [isTorsionPoint_def, ← toPoint_nsmul, ← toPoint_zero]
  exact ⟨fun h => by rw [h], fun h => toPoint_injective h⟩


public theorem natCast_zsmul_eq_zero_iff (n : ℕ) (x : L.AlgPoints hc T) :
    (n : ℤ) • x = 0 ↔ L.IsTorsionPoint _ n (toPoint x) := by
  rw [natCast_zsmul, nsmul_eq_zero_iff]


public theorem toPoint_mem_torsionSubset_iff (n : ℕ) (x : L.AlgPoints hc T) :
    toPoint x ∈ L.torsionSubset _ n ↔ n • x = 0 := by
  rw [mem_torsionSubset, nsmul_eq_zero_iff]


public theorem mem_torsionBy_iff (n : ℕ) (x : L.AlgPoints hc T) :
    x ∈ Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ) ↔ L.IsTorsionPoint _ n (toPoint x) := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul_eq_zero_iff]


@[simp] public theorem torsionByEquiv_apply_coe (n : ℕ)
    (x : Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ)) :
    ((torsionByEquiv n x : L.torsionSubset _ n) : SchemeHomOver _ f) =
      toPoint (x : L.AlgPoints hc T) := rfl


@[simp] public theorem torsionByEquiv_symm_apply_coe (n : ℕ)
    (y : L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n) :
    (((torsionByEquiv n).symm y : Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ)) :
      L.AlgPoints hc T) = ofPoint y.1 := rfl


def torsionByEquiv (n : ℕ) :
    Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ) ≃
      L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n where
  toFun x := ⟨toPoint (x : L.AlgPoints hc T), (mem_torsionBy_iff n _).1 x.2⟩
  invFun y := ⟨ofPoint y.1, (mem_torsionBy_iff n _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem torsionByEquiv_apply_coe (n : ℕ)
    (x : Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ)) :
    ((torsionByEquiv n x : L.torsionSubset _ n) : SchemeHomOver _ f) =
      toPoint (x : L.AlgPoints hc T) := rfl

@[simp] theorem torsionByEquiv_symm_apply_coe (n : ℕ)
    (y : L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n) :
    (((torsionByEquiv n).symm y : Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ)) :
      L.AlgPoints hc T) = ofPoint y.1 := rfl

public theorem natCard_torsionBy (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ)) =
      Nat.card (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n) :=
  Nat.card_congr (torsionByEquiv n)

section Map

variable {T' : Type} [CommRing T'] [Algebra R T'] {T'' : Type} [CommRing T''] [Algebra R T'']


public theorem specMap_comp_algebraMap (a : T →ₐ[R] T') :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R T')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => a.commutes r


@[simp] public theorem mapPoint_coe (a : T →ₐ[R] T')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (mapPoint a x).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ x.1 := rfl


def mapPoint (a : T →ₐ[R] T')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T'))) f :=
  GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom a.toRingHom))
    (specMap_comp_algebraMap a) x

@[simp] theorem mapPoint_coe (a : T →ₐ[R] T')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (mapPoint a x).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ x.1 := rfl

public theorem mapPoint_mul (a : T →ₐ[R] T')
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    mapPoint a (L.mul _ x y) = L.mul _ (mapPoint a x) (mapPoint a y) :=
  L.mul_natural _ _ _ (specMap_comp_algebraMap a) _ _


public theorem mapPoint_one (a : T →ₐ[R] T') :
    mapPoint (f := f) a (L.one _) = L.one _ :=
  L.one_natural _ _ _ (specMap_comp_algebraMap a)


def map (a : T →ₐ[R] T') : L.AlgPoints hc T →+ L.AlgPoints hc T' :=
  AddMonoidHom.mk' (fun x => ofPoint (mapPoint a (toPoint x))) fun x y => by
    apply toPoint_injective
    change mapPoint a (toPoint (x + y)) = L.mul _ (mapPoint a (toPoint x)) (mapPoint a (toPoint y))
    rw [toPoint_add]
    exact mapPoint_mul a _ _

public theorem toPoint_map (a : T →ₐ[R] T') (x : L.AlgPoints hc T) :
    toPoint (map a x) = mapPoint a (toPoint x) := rfl


@[simp] public theorem toPoint_map_coe (a : T →ₐ[R] T') (x : L.AlgPoints hc T) :
    (toPoint (map a x)).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (toPoint x).1 := rfl


public theorem map_ofPoint (a : T →ₐ[R] T')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    map a (ofPoint x : L.AlgPoints hc T) = ofPoint (mapPoint a x) := rfl


public theorem map_id : map (AlgHom.id R T) = AddMonoidHom.id (L.AlgPoints hc T) := by
  refine AddMonoidHom.ext fun x => toPoint_injective (Subtype.ext ?_)
  rw [toPoint_map_coe]
  change Spec.map (CommRingCat.ofHom (RingHom.id T)) ≫ (toPoint x).1 = (toPoint x).1
  rw [CommRingCat.ofHom_id]
  erw [Spec.map_id]
  exact Category.id_comp _


public theorem map_comp (a : T →ₐ[R] T') (b : T' →ₐ[R] T'') :
    map (b.comp a) = (map b).comp (map a : L.AlgPoints hc T →+ L.AlgPoints hc T') := by
  refine AddMonoidHom.ext fun x => toPoint_injective (Subtype.ext ?_)
  rw [toPoint_map_coe, AddMonoidHom.comp_apply, toPoint_map_coe, toPoint_map_coe, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl


public theorem isTorsionPoint_toPoint_map (a : T →ₐ[R] T') (n : ℕ) {x : L.AlgPoints hc T}
    (hx : L.IsTorsionPoint _ n (toPoint x)) : L.IsTorsionPoint _ n (toPoint (map a x)) := by
  rw [← nsmul_eq_zero_iff] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

end Map


public theorem smul_def (σ : T ≃ₐ[R] T) (x : L.AlgPoints hc T) : σ • x = map (σ : T →ₐ[R] T) x := rfl


@[simp] public theorem toPoint_smul_coe (σ : T ≃ₐ[R] T) (x : L.AlgPoints hc T) :
    (toPoint (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : T →ₐ[R] T).toRingHom) ≫ (toPoint x).1 :=
  rfl


public theorem smul_ofPoint (σ : T ≃ₐ[R] T)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    σ • (ofPoint x : L.AlgPoints hc T) = ofPoint (mapPoint (σ : T →ₐ[R] T) x) := rfl


public theorem nsmul_smul_eq_zero (σ : T ≃ₐ[R] T) (n : ℕ) {x : L.AlgPoints hc T} (hx : n • x = 0) :
    n • (σ • x) = 0 := by
  rw [smul_def, ← map_nsmul, hx, map_zero]

end AlgPoints

end RelativeGroupLaw
end GoodReductionJacobian

end
