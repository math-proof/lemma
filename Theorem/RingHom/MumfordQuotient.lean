module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Ring.Action.Group
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Theorem.SimpleGraph.MumfordVertexType
public import Structure.CerednikDrinfeld_MumfordQuotient

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld.Mumford

section Generic

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]


public theorem fracAct_algebraMap [IsDomain M] (g : G) (m : M) :
    fracAct G M g (algebraMap M (FractionRing M) m) = algebraMap M (FractionRing M) (g • m) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ m


public theorem fracAct_one [IsDomain M] : fracAct G M 1 = RingEquiv.refl _ := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [fracAct_algebraMap, one_smul]; rfl


public theorem fracAct_mul [IsDomain M] (g h : G) : fracAct G M (g * h) = (fracAct G M h).trans (fracAct G M g) := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.coe_trans]
  rw [fracAct_algebraMap, fracAct_algebraMap, fracAct_algebraMap, mul_smul]

scoped instance fracMulSemiringAction [IsDomain M] : MulSemiringAction G (FractionRing M) where
  smul g x := fracAct G M g x
  one_smul x := by show fracAct G M 1 x = x; rw [fracAct_one]; rfl
  mul_smul g h x := by show fracAct G M (g * h) x = fracAct G M g (fracAct G M h x); rw [fracAct_mul]; rfl
  smul_zero g := map_zero (fracAct G M g)
  smul_add g x y := map_add (fracAct G M g) x y
  smul_one g := map_one (fracAct G M g)
  smul_mul g x y := map_mul (fracAct G M g) x y


public theorem frac_smul_def [IsDomain M] (g : G) (x : FractionRing M) : g • x = fracAct G M g x := rfl


public theorem frac_smul_algebraMap [IsDomain M] (g : G) (m : M) :
    g • algebraMap M (FractionRing M) m = algebraMap M (FractionRing M) (g • m) :=
  fracAct_algebraMap G M g m


public theorem smul_algebraMap_const_M (g : G) (c : K) : g • algebraMap K M c = algebraMap K M c := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]


public theorem smul_algebraMap_const [IsDomain M] (g : G) (c : K) :
    g • algebraMap K (FractionRing M) c = algebraMap K (FractionRing M) c := by
  rw [IsScalarTower.algebraMap_apply K M (FractionRing M), frac_smul_algebraMap, smul_algebraMap_const_M]

scoped instance fracSMulCommClass [IsDomain M] : SMulCommClass G K (FractionRing M) :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_const]⟩


public theorem mem_invariantField_iff [IsDomain M] (x : FractionRing M) :
    x ∈ invariantField K G M ↔ ∀ g : G, g • x = x := Iff.rfl


public theorem mem_invariantIntermediateField_iff [IsDomain M] (x : FractionRing M) :
    x ∈ invariantIntermediateField K G M ↔ ∀ g : G, g • x = x := Iff.rfl


public theorem invariantField_eq_fixedPoints [IsDomain M] :
    invariantField K G M = FixedPoints.subfield G (FractionRing M) := rfl


public theorem coe_invariantIntermediateField [IsDomain M] :
    (invariantIntermediateField K G M : Set (FractionRing M)) = invariantField K G M := rfl


public theorem mem_invariantFieldOf_iff [IsDomain M] (Γ : Subgroup G) (x : FractionRing M) :
    x ∈ invariantFieldOf K G M Γ ↔ ∀ γ : G, γ ∈ Γ → γ • x = x := Iff.rfl


public theorem algebraMap_invariantFieldOf_coe [IsDomain M] (Γ : Subgroup G) (c : K) :
    ((algebraMap K ↥(invariantFieldOf K G M Γ) c : ↥(invariantFieldOf K G M Γ)) : FractionRing M) =
      algebraMap K (FractionRing M) c := rfl


public theorem invariantFieldOf_top [IsDomain M] : invariantFieldOf K G M ⊤ = invariantField K G M :=
  Subfield.ext fun _ => ⟨fun h g => h g trivial, fun h g _ => h g⟩


public theorem algebraMap_invariantField_coe [IsDomain M] (c : K) :
    ((algebraMap K ↥(invariantField K G M) c : ↥(invariantField K G M)) : FractionRing M) =
      algebraMap K (FractionRing M) c := rfl


public theorem invariantFieldOf_mono_of_le [IsDomain M] {Γ Γ' : Subgroup G} (h : Γ' ≤ Γ) :
    invariantFieldOf K G M Γ ≤ invariantFieldOf K G M Γ' := fun _ hx γ hγ => hx γ (h hγ)


public theorem invariantField_le_invariantFieldOf [IsDomain M] (Γ : Subgroup G) :
    invariantField K G M ≤ invariantFieldOf K G M Γ := fun _ hx γ _ => hx γ


public theorem coe_residualActRingEquiv [IsDomain M] (N : Subgroup G) [N.Normal] (g : G) (x : ↥(invariantFieldOf K G M N)) :
    ((residualActRingEquiv K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) =
      g • (x : FractionRing M) := rfl


public theorem coe_residualAct [IsDomain M] (N : Subgroup G) [N.Normal] (g : G) (x : ↥(invariantFieldOf K G M N)) :
    ((residualAct K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) = g • (x : FractionRing M) := rfl


public theorem residualAct_eq_one_of_mem [IsDomain M] (N : Subgroup G) [N.Normal] {g : G} (hg : g ∈ N) :
    residualAct K G M N g = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (x.2 g hg)


public theorem mem_invariantField_iff_forall_residualAct [IsDomain M] (N : Subgroup G) [N.Normal]
    (x : ↥(invariantFieldOf K G M N)) :
    (x : FractionRing M) ∈ invariantField K G M ↔ ∀ g : G, residualAct K G M N g x = x :=
  ⟨fun h g => Subtype.ext (h g), fun h g => congrArg Subtype.val (h g)⟩


namespace AmbientSemilinearAut

variable {K G M}

section Transport

omit [SMulCommClass G K M]


public theorem fracMap_algebraMap [IsDomain M] (s : AmbientSemilinearAut K G M) (m : M) :
    s.fracMap (algebraMap M (FractionRing M) m) = algebraMap M (FractionRing M) (s.map m) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ m


public theorem fracMap_smul [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G) (x : FractionRing M) :
    s.fracMap (g • x) = g • s.fracMap x := by
  have h : (s.fracMap.toRingHom.comp (fracAct G M g).toRingHom) =
      ((fracAct G M g).toRingHom.comp s.fracMap.toRingHom) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [fracAct_algebraMap, fracMap_algebraMap, fracMap_algebraMap, fracAct_algebraMap, s.map_smul]
  exact congrArg (fun φ : FractionRing M →+* FractionRing M => φ x) h


public theorem fracMap_algebraMap_const [IsDomain M] (s : AmbientSemilinearAut K G M) (c : K) :
    s.fracMap (algebraMap K (FractionRing M) c) = algebraMap K (FractionRing M) (s.base c) := by
  rw [IsScalarTower.algebraMap_apply K M (FractionRing M), fracMap_algebraMap, s.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]


@[ext] public theorem ext {s t : AmbientSemilinearAut K G M} (hb : s.base = t.base) (hm : s.map = t.map) : s = t := by
  cases s; cases t; congr


@[simp] public theorem base_mul (s t : AmbientSemilinearAut K G M) : (s * t).base = t.base.trans s.base := rfl

@[simp] public theorem map_mul_eq (s t : AmbientSemilinearAut K G M) : (s * t).map = t.map.trans s.map := rfl

@[simp] public theorem base_one : (1 : AmbientSemilinearAut K G M).base = RingEquiv.refl K := rfl

@[simp] public theorem map_one_eq : (1 : AmbientSemilinearAut K G M).map = RingEquiv.refl M := rfl


public theorem fracMap_one [IsDomain M] : (1 : AmbientSemilinearAut K G M).fracMap = RingEquiv.refl _ := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [fracMap_algebraMap]; rfl


public theorem fracMap_mul [IsDomain M] (s t : AmbientSemilinearAut K G M) :
    (s * t).fracMap = t.fracMap.trans s.fracMap := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.coe_trans]
  rw [fracMap_algebraMap, fracMap_algebraMap, fracMap_algebraMap]; rfl

end Transport

section Coeff


public theorem coeffAct_baseAut [IsDomain M] (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut.baseAut (coeffAct s) = s.base := rfl


public theorem coe_coeffAct_toRingAut [IsDomain M] (s : AmbientSemilinearAut K G M) (x : ↥(invariantField K G M)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffAct s) x : ↥(invariantField K G M)) : FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl


@[simp] public theorem coeffActHom_apply [IsDomain M] (s : AmbientSemilinearAut K G M) : coeffActHom s = coeffAct s := rfl


public theorem coeffAct_comm_smul [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G) (x : ↥(invariantField K G M)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffAct s) x : ↥(invariantField K G M)) : FractionRing M) =
      s.fracMap (x : FractionRing M) ∧
    s.fracMap (g • (x : FractionRing M)) = g • s.fracMap (x : FractionRing M) :=
  ⟨rfl, fracMap_smul s g x⟩


public theorem fracMap_comm_residualAct [IsDomain M] (s : AmbientSemilinearAut K G M) (N : Subgroup G) [N.Normal] (g : G)
    (x : ↥(invariantFieldOf K G M N)) :
    s.fracMap ((residualAct K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) =
      g • s.fracMap (x : FractionRing M) := by
  rw [coe_residualAct, fracMap_smul]


public theorem coe_invMapOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) (x : ↥(invariantFieldOf K G M Γ)) :
    ((invMapOf Γ s x : ↥(invariantFieldOf K G M Γ)) : FractionRing M) = s.fracMap (x : FractionRing M) := rfl


public theorem coeffActOf_baseAut [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut.baseAut (coeffActOf Γ s) = s.base := rfl


public theorem coe_coeffActOf_toRingAut [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M)
    (x : ↥(invariantFieldOf K G M Γ)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf Γ s) x : ↥(invariantFieldOf K G M Γ)) : FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl


@[simp] public theorem coeffActOfHom_apply [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    coeffActOfHom Γ s = coeffActOf Γ s := rfl


public theorem coeffActOf_comm_residualAct [IsDomain M] (N : Subgroup G) [N.Normal] (s : AmbientSemilinearAut K G M) (g : G)
    (x : ↥(invariantFieldOf K G M N)) :
    AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf N s) (residualAct K G M N g x) =
      residualAct K G M N g (AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf N s) x) :=
  Subtype.ext (by
    rw [coe_coeffActOf_toRingAut, coe_residualAct, coe_residualAct, coe_coeffActOf_toRingAut, fracMap_smul])

end Coeff

end AmbientSemilinearAut

end Generic

section MumfordLayer

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [IsDomain M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]


public theorem mumfordField_le_mumfordFieldPlus : mumfordField K G M ≤ mumfordFieldPlus K G M 𝒯 w₀ :=
  invariantField_le_invariantFieldOf K G M _


public theorem exchangerAct_eq_one_of_mem [(typePreserving G 𝒯 w₀).Normal] {g : G} (hg : g ∈ typePreserving G 𝒯 w₀) :
    exchangerAct K G M 𝒯 w₀ g = 1 :=
  residualAct_eq_one_of_mem K G M _ hg

end MumfordLayer

end CerednikDrinfeld.Mumford

end
