import Mathlib
import sympy.Basic
open CategoryTheory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Rep_exists_coind_inclusion_ker_trace](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_exists_coind_inclusion_ker_trace.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  (U U' : Subgroup G) [U.FiniteIndex] [U'.FiniteIndex]
  (φ : G)
  (X : Rep k G)
  (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X))
  (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
  (ι' : X ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X))
  (τ' : Rep.coind U'.subtype (Rep.res U'.subtype X) ⟶ X)
  {K K' : Rep k G}
  (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X))
  (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K)
  (i' : K' ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X))
  (E' : Rep.coind U'.subtype (Rep.res U'.subtype X) ⟶ K')
  -- given
  (hUU' : U' ≤ U)
  (hι : ∀ (x : X) (g : G), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ g x)
  (hτ : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = (finsum fun c : (G ⧸ U) => X.ρ c.out ((y : G → X) (c.out)⁻¹)))
  (hι' : ∀ (x : X) (g : G), ((ι'.hom x : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = X.ρ g x)
  (hτ' : ∀ y : Rep.coind U'.subtype (Rep.res U'.subtype X), τ'.hom y = (finsum fun c : (G ⧸ U') => X.ρ c.out ((y : G → X) (c.out)⁻¹)))
  (hτi : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = 0 ↔ ∃ κ : K, i.hom κ = y)
  (hi' : Function.Injective i'.hom)
  (hτi' : ∀ y : Rep.coind U'.subtype (Rep.res U'.subtype X), τ'.hom y = 0 ↔ ∃ κ : K', i'.hom κ = y)
  (hE : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((i.hom (E.hom y) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ φ ((y : G → X) (φ⁻¹ * g)) - (y : G → X) g)
  (hE' : ∀ (y : Rep.coind U'.subtype (Rep.res U'.subtype X)) (g : G), ((i'.hom (E'.hom y) : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = X.ρ φ ((y : G → X) (φ⁻¹ * g)) - (y : G → X) g) :
  -- imply
  ∃ (j : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X)) (jK : K ⟶ K'), (∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((j.hom y : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = (y : G → X) g) ∧ jK ≫ i' = i ≫ j ∧ ι ≫ j = ι' ∧ E ≫ jK = j ≫ E' ∧ j ≫ τ' = (U'.relIndex U : k) • τ := by
  -- proof
  classical
  have hmemj : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X),
      ((y : G → X) : G → X) ∈ Representation.coindV U'.subtype (Rep.res U'.subtype X).ρ :=
    fun y u' g => y.2 ⟨(u' : G), hUU' u'.2⟩ g
  let jlin : Rep.coind U.subtype (Rep.res U.subtype X) →ₗ[k] Rep.coind U'.subtype (Rep.res U'.subtype X) :=
    { toFun := fun y => ⟨(y : G → X), hmemj y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let j : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X) :=
    Rep.ofHom (jlin.intertwiningMap_of_isIntertwiningMap (Rep.coind U.subtype (Rep.res U.subtype X)).ρ
      (Rep.coind U'.subtype (Rep.res U'.subtype X)).ρ (fun g y => rfl))
  have hj : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G),
      ((j.hom y : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = (y : G → X) g := fun _ _ => rfl
  let _ : Fintype (G ⧸ U) := Fintype.ofFinite _
  let _ : Fintype (G ⧸ U') := Fintype.ofFinite _
  have hrel : U'.relIndex U ≠ 0 := fun h0 =>
    (Subgroup.FiniteIndex.index_ne_zero (H := U')) (by rw [← Subgroup.relIndex_mul_index hUU', h0, zero_mul])
  let _ : (U'.subgroupOf U).FiniteIndex := ⟨hrel⟩
  let _ : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  have hcardT : Fintype.card (U ⧸ U'.subgroupOf U) = U'.relIndex U := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
    rfl
  have hsum : ∀ (F : G → X), (∀ (g u : G), u ∈ U → F (g * u) = F g) →
      (finsum fun c : (G ⧸ U') => F c.out) = (U'.relIndex U) • (finsum fun c : (G ⧸ U) => F c.out) := by
    intro F hF
    let Fb : G ⧸ U → X := fun c => Quotient.liftOn' c F (fun a b h => by
      rw [QuotientGroup.leftRel_apply] at h
      have : b = a * (a⁻¹ * b) := by group
      rw [this, hF a _ h])
    have hFb : ∀ g : G, Fb (QuotientGroup.mk g) = F g := fun _ => rfl
    have houtU : ∀ c : G ⧸ U, F c.out = Fb c := by
      intro c
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    let eq := Subgroup.quotientEquivProdOfLE hUU'
    have houtU' : ∀ c : G ⧸ U', F c.out = Fb (eq c).1 := by
      intro c
      have h1 : (eq c).1 = QuotientGroup.mk c.out := by
        conv_lhs => rw [← QuotientGroup.out_eq' c]
        rfl
      rw [h1]
      rfl
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp_rw [houtU, houtU']
    rw [Fintype.sum_equiv eq (fun c => Fb (eq c).1) (fun x => Fb x.1) (fun _ => rfl), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, hcardT]
    rw [Finset.smul_sum]
  have htr : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ'.hom (j.hom y) = (U'.relIndex U : k) • τ.hom y := by
    intro y
    rw [hτ', hτ, Nat.cast_smul_eq_nsmul]
    refine hsum (fun g => X.ρ g ((y : G → X) g⁻¹)) (fun g u hu => ?_)
    show X.ρ (g * u) ((y : G → X) (g * u)⁻¹) = X.ρ g ((y : G → X) g⁻¹)
    have hy := y.2 ⟨u⁻¹, U.inv_mem hu⟩ g⁻¹
    have hy' : (y : G → X) (u⁻¹ * g⁻¹) = X.ρ u⁻¹ ((y : G → X) g⁻¹) := hy
    rw [mul_inv_rev, hy', ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hrange : ∀ κ : K, ∃ κ' : K', i'.hom κ' = j.hom (i.hom κ) := by
    intro κ
    apply (hτi' _).1
    rw [htr, (hτi _).2 ⟨κ, rfl⟩, smul_zero]
  choose lift hlift using hrange
  have hlift_add : ∀ a b : K, lift (a + b) = lift a + lift b := by
    intro a b
    apply hi'
    rw [map_add, hlift, hlift, hlift, map_add, map_add]
  have hlift_smul : ∀ (c : k) (a : K), lift (c • a) = c • lift a := by
    intro c a
    apply hi'
    rw [map_smul, hlift, hlift, map_smul, map_smul]
  let jKlin : K →ₗ[k] K' := { toFun := lift, map_add' := hlift_add, map_smul' := hlift_smul }
  have hjKeq : ∀ (g : G) (κ : K), jKlin (K.ρ g κ) = K'.ρ g (jKlin κ) := by
    intro g κ
    apply hi'
    show i'.hom (lift (K.ρ g κ)) = i'.hom (K'.ρ g (lift κ))
    rw [hlift, Rep.hom_comm_apply, Rep.hom_comm_apply, Rep.hom_comm_apply, hlift]
  let jK : K ⟶ K' := Rep.ofHom (jKlin.intertwiningMap_of_isIntertwiningMap K.ρ K'.ρ hjKeq)
  have hjK : ∀ κ : K, i'.hom (jK.hom κ) = j.hom (i.hom κ) := fun κ => hlift κ
  refine ⟨j, jK, hj, ?_, ?_, ?_, ?_⟩
  ·
    rw [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff]
    apply LinearMap.ext
    intro κ
    apply hjK κ
  ·
    rw [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext g
    show ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = ((ι'.hom x : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g
    rw [hι, hι']
  ·
    rw [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff]
    apply LinearMap.ext
    intro y
    apply hi'
    show i'.hom (jK.hom (E.hom y)) = i'.hom (E'.hom (j.hom y))
    rw [hjK]
    apply Subtype.ext
    funext g
    show ((i.hom (E.hom y) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = ((i'.hom (E'.hom (j.hom y)) : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g
    rw [hE, hE']
    rfl
  ·
    rw [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff]
    apply LinearMap.ext
    intro y
    apply htr y


-- created on 2026-10-20
