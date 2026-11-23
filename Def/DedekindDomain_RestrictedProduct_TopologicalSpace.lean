module

public import Mathlib
public import Def.Mathlib_Topology_Algebra_ContinuousMonoidHom
public import Theorem.Set.IsOpenUnits.of.IsOpenSet
public import Theorem.Filter.Algebra.RestrictedProduct.Equiv
public import Theorem.Filter.CountableSetsCofinite
public import Theorem.Filter.SecondCountableBases
public import Instance.Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace

@[expose] public section

section

open RestrictedProduct

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

section groups

variable {S T : ι → Type*}
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

variable [Π i, Monoid (G i)] [Π i, SubmonoidClass (S i) (G i)]
    [Π i, Monoid (H i)] [Π i, SubmonoidClass (T i) (H i)]
    [Π i, TopologicalSpace (G i)]
    [Π i, TopologicalSpace (H i)] in

@[to_additive

                                                                               ]
def ContinuousMulEquiv.restrictedProductCongrRight (φ : (i : ι) → G i ≃ₜ* H i)
    (hφ : ∀ᶠ i in ℱ, Set.BijOn (φ i) (A i) (B i)) :
    (Πʳ i, [G i, A i]_[ℱ]) ≃ₜ* (Πʳ i, [H i, B i]_[ℱ]) where
  toFun := map (fun i ↦ φ i)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo)
  invFun := map (fun i ↦ (φ i).symm)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  map_mul' _ _ := by ext; simp
  left_inv x := by
    ext i
    exact ContinuousMulEquiv.symm_apply_apply _ _
  right_inv x := by
    ext i
    exact ContinuousMulEquiv.apply_symm_apply _ _

end groups

section binary

variable {ι : Type*} {ℱ : Filter ι} {A B : ι → Type*}
  {C : (i : ι) → Set (A i)} {D : (i : ι) → Set (B i)}

def Homeomorph.restrictedProductProd [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (hCopen : ∀ (i : ι), IsOpen (C i)) (hDopen : ∀ (i : ι), IsOpen (D i)) :
    Πʳ i, [A i × B i, C i ×ˢ D i] ≃ₜ (Πʳ i, [A i, C i]) × (Πʳ i, [B i, D i]) where
  __ := Equiv.restrictedProductProd
  continuous_toFun := Equiv.continuous_restrictedProductProd
  continuous_invFun := by
    rw [RestrictedProduct.continuous_dom_prod hCopen hDopen]
    intro S hS
    rw [Equiv.invFun_as_coe, Equiv.restrictedProductProd_symm_comp_inclusion]
    fun_prop

end binary

section pi

variable {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)}

open Filter

def Homeomorph.restrictedProductPi {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)]
    {C : (j : n) → (i : ι) → Set (A j i)} (hCopen : ∀ j i, IsOpen (C j i)) :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}] ≃ₜ Π j, (Πʳ i, [A j i, C j i]) where
  __ := Equiv.restrictedProductPi
  continuous_toFun := Equiv.continuous_restrictedProductPi
  continuous_invFun := by
    rw [RestrictedProduct.continuous_dom_pi hCopen]
    intro S hS
    rw [Equiv.invFun_as_coe, Equiv.restrictedProductPi_symm_comp_inclusion]
    fun_prop

@[to_additive

                                                        ]
def ContinuousMulEquiv.restrictedProductPi {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)] [∀ j i, Group (A j i)]
    {C : (j : n) → (i : ι) → Subgroup (A j i)} (hCopen : ∀ j i, IsOpen (C j i : Set (A j i))) :
    Πʳ i, [Π j, A j i, Subgroup.pi (Set.univ : Set n) (fun j ↦ C j i)] ≃ₜ*
      Π j, (Πʳ i, [A j i, C j i]) where
  toFun x j := map (fun i t ↦ t _)
    (Filter.Eventually.of_forall (fun _ _ ↦ by simp_all [Subgroup.mem_pi])) x
  invFun y := .mk (fun i j ↦ y j i)
    (by have h := fun j ↦ (y j).property; simp [-eventually_cofinite, Subgroup.mem_pi] at h ⊢; exact h)
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; simp [RestrictedProduct.map]
  continuous_toFun := by
    exact continuous_pi fun j ↦
      Continuous.restrictedProduct_congrRight _ fun _ ↦ continuous_apply j
  continuous_invFun := by
    refine (continuous_dom_pi hCopen).mpr fun S hS ↦ ?_
    change Continuous
      (inclusion (fun i ↦ (j : n) → A j i)
        (fun i ↦ Subgroup.pi Set.univ (fun j ↦ C j i)) hS
      ∘ (fun (y : (j : n) → Πʳ (i : ι), [A j i, C j i]_[𝓟 S]) ↦ .mk (fun i j ↦ y j i)
        (by have h := fun j ↦ (y j).property; simp [-eventually_principal, Subgroup.mem_pi] at h ⊢; exact h)))
    exact Continuous.comp (by fun_prop) <|
      continuous_rng_of_principal_iff_forall.mpr fun _ ↦ continuous_pi fun _ ↦
        (RestrictedProduct.continuous_eval _).comp (continuous_apply _)

def Homeomorph.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ i, IsOpen (C i)) :
    Πʳ i, [Matrix m n (A i), (C i).matrix] ≃ₜ Matrix m n (Πʳ i, [A i, C i]) :=
  (Homeomorph.restrictedProductPi (fun _ _ ↦ restrictedProductMatrix_aux _ hCopen)).trans
    (Homeomorph.piCongrRight fun _ ↦ Homeomorph.restrictedProductPi (fun _ ↦ hCopen))

open MulOpposite MonoidHom Units Equiv Set in

@[to_additive

              ]
def Submonoid.unitsContinuousMulEquivUnitsType {M : Type*} [TopologicalSpace M] [Monoid M]
    {S : Submonoid M} (hS : IsOpen (S : Set M)) : S.units ≃ₜ* Sˣ where
  toMulEquiv := S.unitsEquivUnitsType
  continuous_toFun := {
    isOpen_preimage U hU := by
      obtain ⟨t, ht, rfl⟩ := isInducing_embedProduct.isOpen_iff.mpr hU
      let g : Sˣ →* Mˣ := Units.map S.subtype
      have hg : IsOpenMap g := isOpenMap_map (by simp) hS.isOpenMap_subtype_val
      refine ⟨g '' (embedProduct S ⁻¹' t), hg _ (isOpen_induced ht), Set.ext fun s ↦ ?_⟩
      simp only [mem_preimage, mem_image, embedProduct_apply, inv_mk, coeHom_apply, g,
        unitsEquivUnitsType]
      exact ⟨fun ⟨_, ⟨h₁, h₂⟩⟩ ↦ by simp [← h₂, h₁],
        fun h ↦ ⟨S.unitsEquivUnitsType s, by simp [unitsEquivUnitsType, h]⟩⟩
  }
  continuous_invFun := {
    isOpen_preimage U hU := by
      obtain ⟨t, ⟨V, hV, rfl⟩, rfl⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mpr hU
      let f : S × Sᵐᵒᵖ → M × Mᵐᵒᵖ := Prod.map Subtype.val (op ∘ Subtype.val ∘ unop)
      have hf : Continuous f := continuous_subtype_val.fst'.prodMk <| continuous_op.comp' <|
        continuous_subtype_val.comp' <| continuous_unop.comp' continuous_snd
      exact ⟨f ⁻¹' V, hf.isOpen_preimage V hV, rfl⟩
  }

def ContinuousMulEquiv.restrictedProductUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)]
    [(i : ι) → ContinuousMul (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    (A : Π i, S i) (hA : ∀ i, IsOpen (A i : Set (M i))) :
    (Πʳ i, [M i, A i])ˣ ≃ₜ*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units] :=
    have : Fact (∀ i, IsOpen (A i : Set (M i))) := Fact.mk hA
    have hA' : ∀ i, IsOpen ((Submonoid.ofClass (A i)).units : Set (M i)ˣ) :=
      fun i ↦ Set.IsOpenUnits.of.IsOpenSet (hA i)
    have : Fact (∀ i, IsOpen ((Submonoid.ofClass (A i)).units : Set (M i)ˣ)) := Fact.mk hA'

    let sM := structureMapMonoidHom M A cofinite
    let f : ((i : ι) → (A i))ˣ ≃ₜ ((i : ι) → (A i)ˣ) := ContinuousMulEquiv.piUnits.toHomeomorph
    let g : ((i : ι) → (Submonoid.ofClass (A i))ˣ) ≃ₜ ((i : ι) → (Submonoid.ofClass (A i)).units) :=
      Homeomorph.piCongrRight fun i ↦
        (Submonoid.unitsContinuousMulEquivUnitsType (hA i)).symm.toHomeomorph
    let sMx := structureMap (fun i ↦ (M i)ˣ) (fun i ↦ (Submonoid.ofClass (A i)).units) cofinite
  {
  __ := MulEquiv.restrictedProductUnits
  continuous_toFun := by
    apply continuous_of_continuousAt_one MulEquiv.restrictedProductUnits
    intro N hN
    have hN' : (f.trans g) ⁻¹' (sMx ⁻¹' N) ∈ nhds 1 := (f.trans g).continuous.continuousAt
      |>.preimage_mem_nhds <| isEmbedding_structureMap.continuous.continuousAt.preimage_mem_nhds hN
    apply mem_of_superset <| Units.isOpenMap_map (f := sM) isEmbedding_structureMap.injective
      (isOpenEmbedding_structureMap hA).isOpenMap |>.image_mem_nhds hN'
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  continuous_invFun := by
    apply continuous_of_continuousAt_one MulEquiv.restrictedProductUnits.symm
    intro N hN
    have hN' : (Units.map sM) ⁻¹' N ∈ nhds 1 :=
      Units.continuous_map isEmbedding_structureMap.continuous |>.continuousAt.preimage_mem_nhds hN
    apply mem_of_superset <| (isOpenEmbedding_structureMap hA').isOpenMap.image_mem_nhds <|
      (f.trans g).isOpenMap.image_mem_nhds hN'
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hx
      }

set_option backward.isDefEq.respectTransparency false in

def ContinuousMulEquiv.restrictedProductMatrix {ι : Type*}
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, Ring (A i)]
    {C : (i : ι) → Subring (A i)} (hCopen : ∀ i, IsOpen ((C i) : Set (A i))) :
    Matrix n n (Πʳ i, [A i, C i]) ≃ₜ*
      Πʳ i, [Matrix n n (A i), ((C i).matrix : Subring (Matrix n n (A i)))] :=
    let restrictedProductMatrix :
        Matrix n n (Πʳ i, [A i, C i]) ≃ₜ
          Πʳ i, [Matrix n n (A i), ((C i).matrix : Subring (Matrix n n (A i)))] :=
      Homeomorph.symm (Homeomorph.restrictedProductMatrix hCopen)
  {
  __ := restrictedProductMatrix
  map_mul' x y := by
    ext i j k
    rw [mul_apply, Matrix.mul_apply]
    have h {x : Matrix n n Πʳ (i : ι), [A i, ↑(C i)]} {i : ι} {j k : n} :
        (restrictedProductMatrix.toFun x) i j k = (x j k) i := by
      simp [restrictedProductMatrix, Homeomorph.restrictedProductMatrix,
        Homeomorph.restrictedProductPi, Equiv.restrictedProductPi, Matrix]
    simp only [h, Matrix.mul_apply]
    conv_rhs => arg 2; intro _; rw [← mul_apply]
    apply map_sum (RestrictedProduct.evalAddMonoidHom _ _) _ _
      }

def ContinuousMulEquiv.restrictedProductMatrixUnits {ι : Type*}
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, Ring (A i)] [∀ i, IsTopologicalRing (A i)]
    {C : (i : ι) → Subring (A i)} (hCopen : ∀ i, IsOpen ((C i) : Set (A i))) :
    (Matrix n n (Πʳ i, [A i, C i]))ˣ ≃ₜ*
      Πʳ i, [(Matrix n n (A i))ˣ, ((C i).matrix.units : Subgroup (Matrix n n (A i))ˣ)] :=
  (ContinuousMulEquiv.restrictedProductMatrix hCopen).units_map.trans
    (ContinuousMulEquiv.restrictedProductUnits (fun i => (C i).matrix) (fun i => (hCopen i).matrix))

end pi

section flatten

variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)
variable (hf : Filter.comap f 𝒢 = ℱ)

namespace RestrictedProduct

variable [Π i, TopologicalSpace (G i)]

def flatten_homeomorph :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃ₜ
    Πʳ i, [G i, C i]_[ℱ] where
  __ := flatten_equiv C hf
  continuous_toFun := by
    dsimp only [flatten_equiv]
    apply mapAlong_continuous
    fun_prop
  continuous_invFun := by
    dsimp only [flatten_equiv]
    rw [continuous_dom]
    intro S hS
    set T := (f '' Sᶜ)ᶜ with hTval
    have hT : 𝒢 ≤ Filter.principal T := by
      rwa [Filter.le_principal_iff, hTval, ← Filter.mem_comap_iff_compl, hf,
        ← Filter.le_principal_iff]
    let g : Πʳ i, [G i, C i]_[Filter.principal S] → Πʳ j, [Π (i : f ⁻¹' {j}), G i,
        Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[Filter.principal T] :=
      fun x ↦ ⟨fun _ i ↦ x i, by
        have : Filter.comap f (Filter.principal T) ≤ Filter.principal S := by
          rw [Filter.le_principal_iff, Filter.mem_comap]
          use T
          refine ⟨Filter.mem_principal_self T, ?_⟩
          rw [hTval, Set.preimage_compl, Set.compl_subset_comm]
          apply Set.subset_preimage_image
        have hx := Filter.Eventually.filter_mono this x.prop
        rw [Filter.eventually_comap] at hx
        filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
    let hg: Continuous g := by
      rw [continuous_rng_of_principal]
      unfold g
      fun_prop
    apply (continuous_inclusion hT).comp hg

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

def flatten_homeomorph' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃ₜ
    Πʳ i, [G i, C i] :=
  flatten_homeomorph C <|
    le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

end RestrictedProduct

end flatten


section equivs

open Classical Filter in

noncomputable def Homeomorph.restrictedProductPrincipal {ι : Type*}
    (R : ι → Type*) (A : Π i, Set (R i)) [∀ i, TopologicalSpace (R i)] (J : Set ι) :
    Πʳ i, [R i, A i]_[𝓟 J] ≃ₜ (Π i : J, A i) × (Π i : (Jᶜ : Set ι), R i) where
  __ := RestrictedProduct.principalEquivProd R J A
  continuous_toFun := continuous_prodMk.mpr
    ⟨continuous_pi fun _ ↦ continuous_induced_rng.mpr <| continuous_eval _,
      continuous_pi fun _ ↦ continuous_eval _⟩
  continuous_invFun := by
    refine continuous_rng_of_principal.mpr <| continuous_pi fun i ↦ ?_
    by_cases hi : i ∈ J
    · simp only [principalEquivProd, Function.comp_apply, mk_apply, hi, ↓reduceDIte]
      fun_prop
    · simp only [principalEquivProd, Function.comp_apply, mk_apply, hi, ↓reduceDIte]
      fun_prop

open Filter in

@[to_additive

                                      ]
noncomputable def ContinuousMulEquiv.restrictedProductPrincipal {ι : Type*}
    {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {A : Π i, S i}
    (J : Set ι) :
    Πʳ i, [R i, A i]_[𝓟 J] ≃ₜ* (Π i : J, A i) × (Π i : (Jᶜ : Set ι), R i) where
  toHomeomorph := Homeomorph.restrictedProductPrincipal R (fun i ↦ A i) J
  map_mul' _ _ := rfl

end equivs

namespace RestrictedProduct

section single

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddCommMonoid (A i)]
    [(i : ι) → Module R (A i)] [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

variable [∀ i, TopologicalSpace (A i)]
open Filter in

noncomputable def singleContinuousAddMonoidHom (j : ι) : A j →ₜ+ Πʳ i, [A i, B i] where
  __ := singleAddMonoidHom A j
  continuous_toFun := by
    let S : Set ι := {j}ᶜ
    let single' : A j → Πʳ i, [A i, B i]_[𝓟 S] :=
      fun x ↦ ⟨Pi.single j x,
        eventually_principal.mpr
        fun i hi ↦ by simp [Pi.single_eq_of_ne (Set.mem_compl_singleton_iff.mp hi)]⟩
    have : Continuous single' := by
      simp only [continuous_rng_of_principal]
      exact continuous_single j
    apply (isEmbedding_inclusion_principal
      (le_principal_iff.mpr (Set.finite_singleton j).compl_mem_cofinite)).continuous.comp this

end single

section eval

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddCommMonoid (A i)]
    [(i : ι) → Module R (A i)] [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

variable [∀ i, TopologicalSpace (A i)]

def evalContinuousAddMonoidHom (j : ι) : Πʳ i, [A i, B i] →ₜ+ A j := {
  __ := evalAddMonoidHom A j
  continuous_toFun := continuous_eval j
}

end eval

end RestrictedProduct

end

end
