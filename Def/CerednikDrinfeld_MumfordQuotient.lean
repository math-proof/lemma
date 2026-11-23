module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Ring.Action.Group
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Theorem.SimpleGraph.MumfordVertexType
public import Structure.CerednikDrinfeld_MumfordQuotient

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld.Mumford

section Generic

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

def fracAct [IsDomain M] (g : G) : FractionRing M ≃+* FractionRing M :=
  IsFractionRing.ringEquivOfRingEquiv (MulSemiringAction.toRingEquiv G M g)

def invariantIntermediateField [IsDomain M] : IntermediateField K (FractionRing M) :=
  FixedPoints.intermediateField G

def invariantField [IsDomain M] : Subfield (FractionRing M) := (invariantIntermediateField K G M).toSubfield

def invariantIntermediateFieldOf [IsDomain M] (Γ : Subgroup G) : IntermediateField K (FractionRing M) where
  carrier := {x | ∀ γ : G, γ ∈ Γ → γ • x = x}
  mul_mem' {x y} hx hy := fun γ hγ => by rw [smul_mul', hx γ hγ, hy γ hγ]
  one_mem' := fun γ _ => smul_one γ
  add_mem' {x y} hx hy := fun γ hγ => by rw [smul_add, hx γ hγ, hy γ hγ]
  zero_mem' := fun γ _ => smul_zero γ
  algebraMap_mem' c := fun γ _ => smul_algebraMap_const K G M γ c
  inv_mem' x hx := fun γ hγ => by rw [smul_inv'', hx γ hγ]

def invariantFieldOf [IsDomain M] (Γ : Subgroup G) : Subfield (FractionRing M) :=
  (invariantIntermediateFieldOf K G M Γ).toSubfield

def residualActRingEquiv [IsDomain M] (N : Subgroup G) [hN : N.Normal] (g : G) :
    ↥(invariantFieldOf K G M N) ≃+* ↥(invariantFieldOf K G M N) where
  toFun x := ⟨g • (x : FractionRing M), fun n hn => by
    rw [← mul_smul, show n * g = g * (g⁻¹ * n * g) from by group, mul_smul]
    congr 1
    exact x.2 (g⁻¹ * n * g) (by simpa using hN.conj_mem n hn g⁻¹)⟩
  invFun x := ⟨g⁻¹ • (x : FractionRing M), fun n hn => by
    rw [← mul_smul, show n * g⁻¹ = g⁻¹ * (g * n * g⁻¹) from by group, mul_smul]
    congr 1
    exact x.2 (g * n * g⁻¹) (hN.conj_mem n hn g)⟩
  left_inv x := Subtype.ext (inv_smul_smul g (x : FractionRing M))
  right_inv x := Subtype.ext (smul_inv_smul g (x : FractionRing M))
  map_mul' x y := Subtype.ext (smul_mul' g (x : FractionRing M) y)
  map_add' x y := Subtype.ext (smul_add g (x : FractionRing M) y)

def residualAct [IsDomain M] (N : Subgroup G) [N.Normal] :
    G →* (↥(invariantFieldOf K G M N) ≃ₐ[K] ↥(invariantFieldOf K G M N)) where
  toFun g := AlgEquiv.ofRingEquiv (f := residualActRingEquiv K G M N g) (fun c => Subtype.ext (by
    rw [coe_residualActRingEquiv]
    exact smul_algebraMap_const K G M g c))
  map_one' := AlgEquiv.ext fun x => Subtype.ext (one_smul G (x : FractionRing M))
  map_mul' g h := AlgEquiv.ext fun x => Subtype.ext (mul_smul g h (x : FractionRing M))

namespace AmbientSemilinearAut

variable {K G M}

section Transport

omit [SMulCommClass G K M]

def fracMap [IsDomain M] (s : AmbientSemilinearAut K G M) : FractionRing M ≃+* FractionRing M :=
  IsFractionRing.ringEquivOfRingEquiv s.map

end Transport

section Coeff

def invMap [IsDomain M] (s : AmbientSemilinearAut K G M) : ↥(invariantField K G M) ≃+* ↥(invariantField K G M) where
  toFun x := ⟨s.fracMap (x : FractionRing M), fun g => by rw [← fracMap_smul, x.2 g]⟩
  invFun x := ⟨s.fracMap.symm (x : FractionRing M), fun g => by
    apply s.fracMap.injective
    rw [fracMap_smul, RingEquiv.apply_symm_apply, x.2 g]⟩
  left_inv x := Subtype.ext (s.fracMap.symm_apply_apply (x : FractionRing M))
  right_inv x := Subtype.ext (s.fracMap.apply_symm_apply (x : FractionRing M))
  map_mul' x y := Subtype.ext (map_mul s.fracMap (x : FractionRing M) y)
  map_add' x y := Subtype.ext (map_add s.fracMap (x : FractionRing M) y)

def coeffAct [IsDomain M] (s : AmbientSemilinearAut K G M) : AlgebraicCurve.SemilinearAut K ↥(invariantField K G M) :=
  ⟨(s.invMap, s.base), fun c => Subtype.ext (by
    show s.fracMap (algebraMap K (FractionRing M) c) = ((algebraMap K ↥(invariantField K G M) (s.base c) : _) : FractionRing M)
    rw [fracMap_algebraMap_const]; rfl)⟩

def coeffActHom [IsDomain M] : AmbientSemilinearAut K G M →* AlgebraicCurve.SemilinearAut K ↥(invariantField K G M) where
  toFun := coeffAct
  map_one' := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (1 : AmbientSemilinearAut K G M).fracMap (x : FractionRing M) = x
    rw [fracMap_one]; rfl)) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (s * t).fracMap (x : FractionRing M) = s.fracMap (t.fracMap (x : FractionRing M))
    rw [fracMap_mul]; rfl)) rfl)

def invMapOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    ↥(invariantFieldOf K G M Γ) ≃+* ↥(invariantFieldOf K G M Γ) where
  toFun x := ⟨s.fracMap (x : FractionRing M), fun g hg => by rw [← fracMap_smul, x.2 g hg]⟩
  invFun x := ⟨s.fracMap.symm (x : FractionRing M), fun g hg => by
    apply s.fracMap.injective
    rw [fracMap_smul, RingEquiv.apply_symm_apply, x.2 g hg]⟩
  left_inv x := Subtype.ext (s.fracMap.symm_apply_apply (x : FractionRing M))
  right_inv x := Subtype.ext (s.fracMap.apply_symm_apply (x : FractionRing M))
  map_mul' x y := Subtype.ext (map_mul s.fracMap (x : FractionRing M) y)
  map_add' x y := Subtype.ext (map_add s.fracMap (x : FractionRing M) y)

def coeffActOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut K ↥(invariantFieldOf K G M Γ) :=
  ⟨(invMapOf Γ s, s.base), fun c => Subtype.ext (by
    show s.fracMap (algebraMap K (FractionRing M) c) =
      ((algebraMap K ↥(invariantFieldOf K G M Γ) (s.base c) : _) : FractionRing M)
    rw [fracMap_algebraMap_const]; rfl)⟩

def coeffActOfHom [IsDomain M] (Γ : Subgroup G) :
    AmbientSemilinearAut K G M →* AlgebraicCurve.SemilinearAut K ↥(invariantFieldOf K G M Γ) where
  toFun := coeffActOf Γ
  map_one' := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (1 : AmbientSemilinearAut K G M).fracMap (x : FractionRing M) = x
    rw [fracMap_one]; rfl)) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (s * t).fracMap (x : FractionRing M) = s.fracMap (t.fracMap (x : FractionRing M))
    rw [fracMap_mul]; rfl)) rfl)

end Coeff

end AmbientSemilinearAut

end Generic

section MumfordLayer

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [IsDomain M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

abbrev mumfordField : Subfield (FractionRing M) := invariantField K G M

variable {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W)

def HasTypeExchanger : Prop := ∃ g : G, g ∉ typePreserving G 𝒯 w₀

abbrev mumfordFieldPlus : Subfield (FractionRing M) := invariantFieldOf K G M (typePreserving G 𝒯 w₀)

abbrev exchangerAct [(typePreserving G 𝒯 w₀).Normal] :
    G →* (↥(mumfordFieldPlus K G M 𝒯 w₀) ≃ₐ[K] ↥(mumfordFieldPlus K G M 𝒯 w₀)) :=
  residualAct K G M (typePreserving G 𝒯 w₀)

end MumfordLayer

end CerednikDrinfeld.Mumford

end

end
