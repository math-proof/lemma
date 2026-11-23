module

public import Mathlib
public import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
public import Instance.GoodReductionJacobian_RelativeGroupLawKerPair

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra Scheme

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section IsHom

variable {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}


public theorem mul {ψ : SchemeHomOver f f'} (h : IsHom G G' ψ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (G.mul t x y) ψ =
      G'.mul t (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ) :=
  h t x y


public theorem one {ψ : SchemeHomOver f f'} (h : IsHom G G' ψ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (G.one t) ψ = G'.one t := by
  letI := G'.pointGroup t
  have h2 : NeronModelInfra.schemeHomOverComp (G.one t) ψ * NeronModelInfra.schemeHomOverComp (G.one t) ψ =
      NeronModelInfra.schemeHomOverComp (G.one t) ψ := by
    show G'.mul t _ _ = _
    rw [← h t, G.one_mul]
  exact mul_eq_left.mp h2


public theorem inv {ψ : SchemeHomOver f f'} (h : IsHom G G' ψ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (G.inv t x) ψ = G'.inv t (NeronModelInfra.schemeHomOverComp x ψ) := by
  letI := G'.pointGroup t
  have h2 : NeronModelInfra.schemeHomOverComp (G.inv t x) ψ * NeronModelInfra.schemeHomOverComp x ψ = 1 := by
    show G'.mul t _ _ = G'.one t
    rw [← h t, G.inv_mul_cancel, h.one]
  exact eq_inv_of_mul_eq_one_left h2


public theorem id (G : RelativeGroupLaw R f) : IsHom G G (NeronModelInfra.schemeHomOverId f) := by
  intro T t x y
  simp only [NeronModelInfra.schemeHomOverComp_id_right]


public theorem comp {ψ : SchemeHomOver f f'} {χ : SchemeHomOver f' f''} (hψ : IsHom G G' ψ) (hχ : IsHom G' G'' χ) :
    IsHom G G'' (NeronModelInfra.schemeHomOverComp ψ χ) := by
  intro T t x y
  rw [← NeronModelInfra.schemeHomOverComp_assoc, hψ t, hχ t, NeronModelInfra.schemeHomOverComp_assoc,
    NeronModelInfra.schemeHomOverComp_assoc]

end IsHom


public theorem IsHom.fibreRestrictAlong {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {Gg : RelativeGroupLaw R g} {Gf : RelativeGroupLaw R f}
    {ψ : SchemeHomOver g f} (h : IsHom Gg Gf ψ) :
    IsHom (Gg.baseChange ι) (Gf.baseChange ι) (NeronSpecialFibreInfra.fibreRestrictAlong ι f g ψ) := by
  intro T t x y
  apply (baseChangePointEquiv ι (f := f) t).injective
  show baseChangePointToBase ι _ = baseChangePointToBase ι _
  rw [baseChangePointToBase_comp_fibreRestrictAlong, baseChange_mul, baseChange_mul,
    baseChangePointToBase_ofBase, baseChangePointToBase_ofBase, h,
    baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_comp_fibreRestrictAlong]

end IsHom

section KerPair

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}


public theorem kerLeg_snd_eq (i : Fin 2) :
    pullback.snd (φ i).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 =
      pullback.fst (φ i).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f := by
  have h1 := pullback.condition (f := (φ i).1) (g := (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)
  have h2 := congrArg (· ≫ f') h1
  simp only [Category.assoc, (φ i).2, (G'.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id] at h2
  exact h2.symm


@[reassoc]
public theorem kerPair_snd_fst :
    pullback.snd (pullback.fst (φ 0).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)
        (pullback.fst (φ 1).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫
      pullback.fst (φ 1).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 = kerPairι G' φ :=
  pullback.condition.symm


public theorem kerPairι_comp (i : Fin 2) :
    kerPairι G' φ ≫ (φ i).1 = kerPairStr G' φ ≫ (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  fin_cases i
  · show (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (φ 0).1 = ((pullback.fst _ _ ≫ pullback.fst _ _) ≫ f) ≫ _
    simp only [Category.assoc]
    rw [pullback.condition (f := (φ 0).1), kerLeg_snd_eq G' φ 0, Category.assoc]
  · show kerPairι G' φ ≫ (φ 1).1 = (kerPairι G' φ ≫ f) ≫ _
    rw [← kerPair_snd_fst]
    simp only [Category.assoc]
    rw [pullback.condition (f := (φ 1).1), kerLeg_snd_eq G' φ 1, Category.assoc]


public theorem one_coe_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G'.one t).1 = t ≫ (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := G'.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h, schemeHomOverComp_coe]


public theorem kerPairι_mem {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t (kerPairStr G' φ))
    (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (⟨z.1 ≫ kerPairι G' φ, by rw [Category.assoc]; exact z.2⟩ : SchemeHomOver t f)
      (φ i) = G'.one t := by
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, one_coe_eq, Category.assoc, kerPairι_comp, ← Category.assoc, z.2]


@[simp]
public theorem kerPairLift_ι {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f)
    (hx : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t) :
    kerPairLift G' φ x hx ≫ kerPairι G' φ = x.1 := by
  simp only [kerPairLift, ← Category.assoc, pullback.lift_fst]


@[simp]
public theorem kerPairPointEquiv_apply_coe_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t (kerPairStr G' φ)) :
    ((kerPairPointEquiv G' φ t z).1).1 = z.1 ≫ kerPairι G' φ :=
  rfl


@[simp]
public theorem kerPairPointEquiv_symm_apply_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : {x : SchemeHomOver t f // ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t}) :
    ((kerPairPointEquiv G' φ t).symm x).1 ≫ kerPairι G' φ = x.1.1 :=
  kerPairLift_ι G' φ x.1 x.2


public theorem kerPairPointEquiv_apply_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t z).1 = NeronModelInfra.schemeHomOverComp z (kerPairιOver G' φ) :=
  rfl


public theorem kerPairPointEquiv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (z : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t' (schemeHomOverComp ψ hψ z)).1 =
      schemeHomOverComp ψ hψ (kerPairPointEquiv G' φ t z).1 :=
  Subtype.ext (Category.assoc _ _ _)


public theorem kerPairPoint_ext {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {z w : SchemeHomOver t (kerPairStr G' φ)}
    (h : z.1 ≫ kerPairι G' φ = w.1 ≫ kerPairι G' φ) : z = w :=
  (kerPairPointEquiv G' φ t).injective (Subtype.ext (Subtype.ext h))

end KerPair

section KerPairLaw

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
variable (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')
  (hφ : ∀ i, IsHom G G' (φ i))

section

variable {G G' φ}
include hφ


public theorem kerPair_mul_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {x y : SchemeHomOver t f}
    (hx : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t)
    (hy : ∀ i, NeronModelInfra.schemeHomOverComp y (φ i) = G'.one t) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (G.mul t x y) (φ i) = G'.one t := by
  rw [hφ i t, hx i, hy i, G'.one_mul]


public theorem kerPair_one_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (G.one t) (φ i) = G'.one t :=
  IsHom.one (hφ i) t


public theorem kerPair_inv_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {x : SchemeHomOver t f}
    (hx : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (G.inv t x) (φ i) = G'.one t := by
  letI := G'.pointGroup t
  rw [IsHom.inv (hφ i) t, hx i]
  exact inv_one

end


@[simp]
public theorem kerPairPointEquiv_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z w : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t ((kerPairLaw G G' φ hφ).mul t z w)).1 =
      G.mul t (kerPairPointEquiv G' φ t z).1 (kerPairPointEquiv G' φ t w).1 := by
  simp only [kerPairLaw, Equiv.apply_symm_apply]


@[simp]
public theorem kerPairPointEquiv_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (kerPairPointEquiv G' φ t ((kerPairLaw G G' φ hφ).one t)).1 = G.one t := by
  simp only [kerPairLaw, Equiv.apply_symm_apply]


@[simp]
public theorem kerPairPointEquiv_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t ((kerPairLaw G G' φ hφ).inv t z)).1 =
      G.inv t (kerPairPointEquiv G' φ t z).1 := by
  simp only [kerPairLaw, Equiv.apply_symm_apply]


public theorem kerPairι_isHom : IsHom (kerPairLaw G G' φ hφ) G (kerPairιOver G' φ) := by
  intro T t x y
  rw [← kerPairPointEquiv_apply_coe, kerPairPointEquiv_mul, kerPairPointEquiv_apply_coe, kerPairPointEquiv_apply_coe]


public theorem IsCommutative.kerPairLaw (hc : G.IsCommutative) : (kerPairLaw G G' φ hφ).IsCommutative := by
  intro T t x y
  apply (kerPairPointEquiv G' φ t).injective
  apply Subtype.ext
  rw [kerPairPointEquiv_mul, kerPairPointEquiv_mul, hc t]


public theorem kerPairPointEquiv_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (z : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t ((kerPairLaw G G' φ hφ).nsmul t n z)).1 = G.nsmul t n (kerPairPointEquiv G' φ t z).1 := by
  induction n with
  | zero => simp only [nsmul_zero, kerPairPointEquiv_one]
  | succ n ih => simp only [nsmul_succ, kerPairPointEquiv_mul, ih]

end KerPairLaw

section Properties

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
variable (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')


public theorem isClosedImmersion_one [IsSeparated f'] :
    IsClosedImmersion (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have : IsClosedImmersion ((G'.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f') := by
    rw [(G'.one (𝟙 (Spec (CommRingCat.of R)))).2]; infer_instance
  exact .of_comp _ f'

end Properties

end RelativeGroupLaw
end GoodReductionJacobian

end
