import Mathlib.AlgebraicGeometry.Limits
import Lemma.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Lemma.Definitions.Def_AlgebraicCurve_SymmetricPower

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)

noncomputable abbrev fibrePowOver : Scheme.{u} :=
  widePullback S (fun _ : Fin r => 𝒞) (fun _ => f)

namespace fibrePowOver

noncomputable abbrev proj (i : Fin r) : fibrePowOver f r ⟶ 𝒞 :=
  WidePullback.π (fun _ : Fin r => f) i

noncomputable abbrev toBase : fibrePowOver f r ⟶ S :=
  WidePullback.base (fun _ : Fin r => f)

@[reassoc (attr := simp)]
theorem proj_comp (i : Fin r) : proj f r i ≫ f = toBase f r :=
  WidePullback.π_arrow _ _

end fibrePowOver

variable {r} {T : Scheme.{u}} {g : T ⟶ S}

noncomputable def prodKerGraph (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    (pullback f g).IdealSheafData :=
  ∏ i, (graphOver f (a i) (ha i)).ker

theorem prodKerGraph_eq_prod (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f a ha = ∏ i, (graphOver f (a i) (ha i)).ker :=
  rfl

@[simp] theorem prodKerGraph_zero (a : Fin 0 → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f a ha = ⊤ := by
  simp [prodKerGraph]

@[simp] theorem prodKerGraph_one (a : Fin 1 → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f a ha = (graphOver f (a 0) (ha 0)).ker := by
  simp [prodKerGraph]

theorem prodKerGraph_succ (a : Fin (r + 1) → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f a ha =
      (graphOver f (a 0) (ha 0)).ker * prodKerGraph f (fun i => a i.succ) (fun i => ha i.succ) := by
  simp [prodKerGraph, Fin.prod_univ_succ]

theorem prodKerGraph_comp_equiv (σ : Equiv.Perm (Fin r)) (a : Fin r → (T ⟶ 𝒞))
    (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f (fun i => a (σ i)) (fun i => ha (σ i)) = prodKerGraph f a ha :=
  Equiv.prod_comp σ (fun i => (graphOver f (a i) (ha i)).ker)

theorem ideal_prodKerGraph (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g)
    (U : (pullback f g).affineOpens) :
    (prodKerGraph f a ha).ideal U = ∏ i, (graphOver f (a i) (ha i)).ker.ideal U := by
  classical
  unfold prodKerGraph
  induction (Finset.univ : Finset (Fin r)) using Finset.cons_induction with
  | empty => simp [Ideal.one_eq_top]
  | cons i s hi ih => rw [Finset.prod_cons, Finset.prod_cons, ← ih]; rfl

def SameDivisor (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) (b : Fin r → (T ⟶ 𝒞))
    (hb : ∀ i, b i ≫ f = g) : Prop :=
  prodKerGraph f a ha = prodKerGraph f b hb

namespace SameDivisor

variable {f}

theorem iff {a : Fin r → (T ⟶ 𝒞)} {ha : ∀ i, a i ≫ f = g} {b : Fin r → (T ⟶ 𝒞)}
    {hb : ∀ i, b i ≫ f = g} :
    SameDivisor f a ha b hb ↔ prodKerGraph f a ha = prodKerGraph f b hb :=
  Iff.rfl

theorem refl (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) : SameDivisor f a ha a ha :=
  Eq.refl _

theorem rfl {a : Fin r → (T ⟶ 𝒞)} {ha : ∀ i, a i ≫ f = g} : SameDivisor f a ha a ha :=
  Eq.refl _

theorem symm {a : Fin r → (T ⟶ 𝒞)} {ha : ∀ i, a i ≫ f = g} {b : Fin r → (T ⟶ 𝒞)}
    {hb : ∀ i, b i ≫ f = g} (h : SameDivisor f a ha b hb) : SameDivisor f b hb a ha :=
  Eq.symm h

theorem trans {a : Fin r → (T ⟶ 𝒞)} {ha : ∀ i, a i ≫ f = g} {b : Fin r → (T ⟶ 𝒞)}
    {hb : ∀ i, b i ≫ f = g} {c : Fin r → (T ⟶ 𝒞)} {hc : ∀ i, c i ≫ f = g}
    (h₁ : SameDivisor f a ha b hb) (h₂ : SameDivisor f b hb c hc) : SameDivisor f a ha c hc :=
  Eq.trans h₁ h₂

theorem comp_equiv (σ : Equiv.Perm (Fin r)) (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    SameDivisor f (fun i => a (σ i)) (fun i => ha (σ i)) a ha :=
  prodKerGraph_comp_equiv f σ a ha

end SameDivisor

section Empty

theorem Scheme.Hom.finrank_eq_zero_of_isEmpty {X Y : Scheme.{u}} (π : X ⟶ Y) [IsEmpty X]
    (y : Y) : π.finrank y = 0 := by
  obtain ⟨R, i, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  rw [← Scheme.Hom.finrank_pullback_snd]
  have : IsEmpty ↥(pullback π i) := Function.isEmpty (pullback.fst π i)
  rw [← Scheme.Hom.finrank_comp_left_of_isIso (pullback π i).isoSpec.inv]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback π i).isoSpec.inv ≫ pullback.snd π i)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hflat : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hfin
  rw [Flat.SpecMap_iff] at hflat
  rw [← hφ, Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat]
  algebraize [φ.hom]
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]
  rw [Module.rankAtStalk_eq_zero_of_subsingleton]
  rfl

noncomputable def RelEffCartierDiv.empty (g : T ⟶ S) : RelEffCartierDiv f 0 g where
  I := ⊤
  isFinite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance
  finrank_eq t := Scheme.Hom.finrank_eq_zero_of_isEmpty _ t

@[simp] theorem RelEffCartierDiv.empty_I (g : T ⟶ S) : (RelEffCartierDiv.empty f g).I = ⊤ :=
  rfl

variable {f}

theorem RelEffCartierDiv.I_eq_top_of_degree_zero (D : RelEffCartierDiv f 0 g) : D.I = ⊤ := by
  have := D.isFinite
  have := D.flat
  have hempty : IsEmpty ↥D.I.subscheme := by
    by_contra h
    rw [not_isEmpty_iff] at h
    obtain ⟨x⟩ := h
    have h1 := Scheme.Hom.one_le_finrank_map (D.I.subschemeι ≫ pullback.snd f g) x
    rw [D.finrank_eq] at h1
    exact Nat.not_succ_le_zero 0 h1
  rw [← D.I.ker_subschemeι]
  exact Scheme.ker_eq_top_of_isEmpty _

instance RelEffCartierDiv.subsingleton_of_degree_zero : Subsingleton (RelEffCartierDiv f 0 g) :=
  ⟨fun D E => RelEffCartierDiv.ext (by rw [D.I_eq_top_of_degree_zero, E.I_eq_top_of_degree_zero])⟩

theorem RelEffCartierDiv.eq_empty (D : RelEffCartierDiv f 0 g) : D = RelEffCartierDiv.empty f g :=
  Subsingleton.elim _ _

end Empty

namespace fibrePowOver

variable (r)

noncomputable abbrev tautIdeal : (pullback f (toBase f r)).IdealSheafData :=
  prodKerGraph f (proj f r) (proj_comp f r)

end fibrePowOver

section FieldComparison

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)

theorem fibrePowOver_eq_finFibrePow : fibrePowOver c r = finFibrePow c r := rfl

theorem fibrePowOver.proj_eq_finFibrePow_proj (i : Fin r) :
    fibrePowOver.proj c r i = finFibrePow.proj c r i := rfl

theorem fibrePowOver.toBase_eq_finFibrePow_toBase :
    fibrePowOver.toBase c r = finFibrePow.toBase c r := rfl

theorem fibrePowOver.tautIdeal_eq_prod_ker_lift :
    fibrePowOver.tautIdeal c r = ∏ i : Fin r,
      (pullback.lift (WidePullback.π (fun _ : Fin r => c) i) (𝟙 (finFibrePow c r))
        (by rw [Category.id_comp]; exact WidePullback.π_arrow _ i)).ker := rfl

end FieldComparison

end AlgebraicGeometry
