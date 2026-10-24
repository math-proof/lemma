/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.HarishChandraIsomorphism
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm

noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
variable {R 𝔤}

structure ChevalleyRestrictionData (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) where
  S𝔤 : Type*
  [instRing : Ring S𝔤]
  [instAlgebra : Algebra R S𝔤]
  adInvariant : Subalgebra R S𝔤
  restrictionAlgHom : S𝔤 →ₐ[R] UniversalEnvelopingAlgebra R Δ.𝔥
  algActionOnS𝔤 : wg.W →* (S𝔤 ≃ₐ[R] S𝔤)
  restriction_equivariant :
    ∀ (w : wg.W) (f : S𝔤),
      restrictionAlgHom ((algActionOnS𝔤 w) f) =
      (wg.algAction w) (restrictionAlgHom f)
  adInvariant_W_fixed :
    ∀ (w : wg.W) (f : S𝔤), f ∈ adInvariant →
      (algActionOnS𝔤 w) f = f
  eval𝔤 : S𝔤 → (𝔤 → R)
  eval𝔥 : UniversalEnvelopingAlgebra R Δ.𝔥 → (Δ.𝔥 → R)
  eval𝔤_injective : Function.Injective eval𝔤
  eval𝔥_injective : Function.Injective eval𝔥
  eval_restriction_compat : ∀ (f : S𝔤) (h : Δ.𝔥),
      eval𝔥 (restrictionAlgHom f) h = eval𝔤 f (h : 𝔤)
  adInvariant_eval_determined_by_h : ∀ (f₁ f₂ : S𝔤),
      f₁ ∈ adInvariant → f₂ ∈ adInvariant →
      (∀ h : Δ.𝔥, eval𝔤 f₁ (h : 𝔤) = eval𝔤 f₂ (h : 𝔤)) →
      ∀ x : 𝔤, eval𝔤 f₁ x = eval𝔤 f₂ x
  trace_function_surjectivity : ∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥),
      p ∈ wg.invariantSubalgebra →
      ∃ f : S𝔤, f ∈ adInvariant ∧
        ∀ h : Δ.𝔥, eval𝔥 (restrictionAlgHom f) h = eval𝔥 p h

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

noncomputable def killingFormDualIso
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    Δ.𝔥 ≃ₗ[R] (Δ.𝔥 →ₗ[R] R) := by
  haveI : Δ.𝔥.IsCartanSubalgebra := Δ.is_cartan
  exact LieAlgebra.IsKilling.cartanEquivDual Δ.𝔥

noncomputable def TriangularDecomposition.projectToH
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (x : 𝔤) : Δ.𝔥 :=
  (Δ.decomp_exists x).choose_spec.choose

noncomputable def chevalleyEval𝔥
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (p : UniversalEnvelopingAlgebra R Δ.𝔥) (h : Δ.𝔥) : R :=
  evalWeight Δ (killingFormDualIso Δ h) p

noncomputable def chevalleyEval𝔤
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (f : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))) (x : 𝔤) : R :=
  chevalleyEval𝔥 Δ (HarishChandraAlgHom Δ f) (Δ.projectToH x)

noncomputable def chevalleyRestrictionData
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ) :
    ChevalleyRestrictionData Δ wg where
  S𝔤 := ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
  instRing := inferInstance
  instAlgebra := inferInstance
  adInvariant := ⊤
  restrictionAlgHom := HarishChandraAlgHom Δ
  algActionOnS𝔤 := 1
  restriction_equivariant := fun w f => by
    simp only [MonoidHom.one_apply, AlgEquiv.one_apply]
    exact (harishChandra_maps_to_W_invariants Δ wg f w).symm
  adInvariant_W_fixed := fun w f _ => by
    simp only [MonoidHom.one_apply, AlgEquiv.one_apply]
  eval𝔤 := chevalleyEval𝔤 Δ
  eval𝔥 := chevalleyEval𝔥 Δ
  eval𝔤_injective := by
    intro f₁ f₂ heval
    have h_eval_h : ∀ h : Δ.𝔥, chevalleyEval𝔥 Δ (HarishChandraAlgHom Δ f₁) h =
        chevalleyEval𝔥 Δ (HarishChandraAlgHom Δ f₂) h := by
      intro h
      have := congr_fun heval (h : 𝔤)
      simp only [chevalleyEval𝔤, Δ.projectToH_of_mem_h h] at this
      exact this
    have h_hc_eq : HarishChandraAlgHom Δ f₁ = HarishChandraAlgHom Δ f₂ := by
      apply evalWeight_separates
      intro wt
      have h_surj := (killingFormDualIso Δ).surjective wt
      obtain ⟨h, rfl⟩ := h_surj
      exact h_eval_h h
    exact harishChandra_center_injective Δ wg f₁ f₂ (by
      show HarishChandraMap Δ (f₁ : UniversalEnvelopingAlgebra R 𝔤) =
           HarishChandraMap Δ (f₂ : UniversalEnvelopingAlgebra R 𝔤)

      exact h_hc_eq)
  eval𝔥_injective := by
    intro p₁ p₂ heval
    apply evalWeight_separates
    intro wt
    obtain ⟨h, rfl⟩ := (killingFormDualIso Δ).surjective wt
    exact congr_fun heval h
  eval_restriction_compat := fun f h => by
    simp only [chevalleyEval𝔤, chevalleyEval𝔥]
    rw [Δ.projectToH_of_mem_h h]
  adInvariant_eval_determined_by_h := fun f₁ f₂ _ _ h_agree x => by
    simp only [chevalleyEval𝔤] at h_agree ⊢

    simp only [Δ.projectToH_of_mem_h] at h_agree

    exact h_agree (Δ.projectToH x)
  trace_function_surjectivity := fun p hp => by
    obtain ⟨c, hc⟩ := (harishChandra_bijectivity Δ wg).2 p hp
    refine ⟨c, Algebra.mem_top, fun h => ?_⟩
    simp only [chevalleyEval𝔥]
    have : (HarishChandraAlgHom Δ) c = p := hc
    rw [this]

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_lands_in_W_invariants_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg)
    (f : crd.S𝔤) (hf : f ∈ crd.adInvariant) :
    (crd.restrictionAlgHom f) ∈
      (wg.invariantSubalgebra : Set (UniversalEnvelopingAlgebra R Δ.𝔥)) := by


  intro w
  rw [← crd.restriction_equivariant w f, crd.adInvariant_W_fixed w f hf]

def ChevalleyRestrictionData.restrictionMap
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    crd.adInvariant →ₐ[R] wg.invariantSubalgebra :=
  (crd.restrictionAlgHom.comp crd.adInvariant.val).codRestrict
    wg.invariantSubalgebra (fun ⟨x, hx⟩ =>
      chevalley_restriction_lands_in_W_invariants_aux crd x hx)

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_injective_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    Function.Injective crd.restrictionMap := by
  intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ heq
  have h_res : crd.restrictionAlgHom f₁ = crd.restrictionAlgHom f₂ := by
    have := congr_arg Subtype.val heq
    simpa [ChevalleyRestrictionData.restrictionMap, AlgHom.codRestrict] using this
  have h_eval_h : ∀ h : Δ.𝔥, crd.eval𝔤 f₁ (h : 𝔤) = crd.eval𝔤 f₂ (h : 𝔤) := by
    intro h
    rw [← crd.eval_restriction_compat f₁ h, ← crd.eval_restriction_compat f₂ h, h_res]
  have h_eval_all : ∀ x : 𝔤, crd.eval𝔤 f₁ x = crd.eval𝔤 f₂ x :=
    crd.adInvariant_eval_determined_by_h f₁ f₂ hf₁ hf₂ h_eval_h
  have h_eq : f₁ = f₂ := crd.eval𝔤_injective (funext h_eval_all)
  exact Subtype.ext h_eq

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_surjective_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    Function.Surjective crd.restrictionMap := by
  intro ⟨p, hp⟩
  obtain ⟨f, hf_inv, hf_eval⟩ := crd.trace_function_surjectivity p hp
  have h_eq : crd.restrictionAlgHom f = p :=
    crd.eval𝔥_injective (funext hf_eval)
  exact ⟨⟨f, hf_inv⟩, Subtype.ext h_eq⟩

theorem chevalley_restriction_injective
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ} :
    Function.Injective (chevalleyRestrictionData wg).restrictionMap :=
  chevalley_restriction_injective_aux (chevalleyRestrictionData wg)

theorem chevalley_restriction_surjective
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ} :
    Function.Surjective (chevalleyRestrictionData wg).restrictionMap :=
  chevalley_restriction_surjective_aux (chevalleyRestrictionData wg)

theorem chevalley_restriction_bijective
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ} :
    Function.Bijective (chevalleyRestrictionData wg).restrictionMap :=
  ⟨chevalley_restriction_injective, chevalley_restriction_surjective⟩

noncomputable def chevalleyRestrictionAlgEquiv
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ} :
    (chevalleyRestrictionData wg).adInvariant ≃ₐ[R] wg.invariantSubalgebra :=
  AlgEquiv.ofBijective (chevalleyRestrictionData wg).restrictionMap
    chevalley_restriction_bijective

structure IsComplexReflection {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (g : V ≃ₗ[k] V) : Prop where
  rank_eq_one : Module.finrank k (LinearMap.range ((g : V →ₗ[k] V) - LinearMap.id)) = 1
  ne_id : g ≠ LinearEquiv.refl k V

structure IsComplexReflectionGroup {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (G : Type*) [Group G] [Fintype G]
    (ρ : G →* V ≃ₗ[k] V) : Prop where
  generated_by_reflections :
    ∀ g : G, ∃ (n : ℕ) (reflections : Fin n → G),
      (∀ i, IsComplexReflection (ρ (reflections i))) ∧
      g = (List.ofFn reflections).prod

def polynomialInvariantSubalgebra (k : Type*) [CommSemiring k]
    (G : Type*) [Group G] (ι : Type*)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)) :
    Subalgebra k (MvPolynomial ι k) :=
  Subalgebra.invariants G algAct

def IsInducedPolynomialAction {k : Type*} [CommRing k]
    {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V)
    (G : Type*) [Group G]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)) : Prop :=
  ∀ (g : G) (i : ι),
    algAct g (MvPolynomial.X i) =
    Finset.univ.sum fun j =>
      MvPolynomial.C (b.repr (ρ g (b i)) j) * MvPolynomial.X j

def IsPolynomialAlgebra {R : Type*} [CommSemiring R]
    (A : Type*) [Semiring A] [Algebra R A] : Prop :=
  ∃ (n : ℕ), Nonempty (MvPolynomial (Fin n) R ≃ₐ[R] A)

noncomputable def orbitPoly {k : Type*} [Field k]
    {G : Type*} [Group G] [Fintype G] {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) : Polynomial (MvPolynomial ι k) :=
  Finset.univ.prod (fun g => Polynomial.X - Polynomial.C ((algAct g) p))

structure ChevalleyRestrictionPolyData
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ)
    (n m : ℕ) where
  G : Type*
  [instGroupG : Group G]


  G_action : G →* (MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R)
  W_action : wg.W →* (MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin m) R)
  Res : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin m) R
  Res_components : Fin n → MvPolynomial (Fin m) R
  Res_eq_aeval : Res = MvPolynomial.aeval Res_components
  Res_components_homogeneous : ∀ i, (Res_components i).IsHomogeneous 1
  Res_action_compat : ∀ (w : wg.W), ∃ (g : G),
    ∀ (p : MvPolynomial (Fin n) R),
      Res ((G_action g) p) = (W_action w) (Res p)
  kernel_trivial : ∀ (p : MvPolynomial (Fin n) R),
    p ∈ Subalgebra.invariants G G_action → Res p = 0 → p = 0


attribute [instance] ChevalleyRestrictionPolyData.instGroupG

def ChevalleyRestrictionPolyData.restrictionMapPoly
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m) :
    Subalgebra.invariants cpd.G cpd.G_action →ₐ[R]
    Subalgebra.invariants wg.W cpd.W_action :=
  (cpd.Res.comp (Subalgebra.invariants cpd.G cpd.G_action).val).codRestrict
    (Subalgebra.invariants wg.W cpd.W_action)
    (fun ⟨x, hx⟩ => cpd.Res_maps_invariants x hx)

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_polynomial
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m) :
    Function.Bijective cpd.restrictionMapPoly := by
  constructor
  ·
    intro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ heq

    have h_res : cpd.Res p₁ = cpd.Res p₂ := by
      have := congr_arg Subtype.val heq
      simpa [ChevalleyRestrictionPolyData.restrictionMapPoly, AlgHom.codRestrict] using this

    have hker : cpd.Res (p₁ - p₂) = 0 := by rw [map_sub, h_res, sub_self]

    have hinv : (p₁ - p₂) ∈ Subalgebra.invariants cpd.G cpd.G_action := by
      intro g; simp [map_sub, hp₁ g, hp₂ g]

    have h0 := cpd.kernel_trivial (p₁ - p₂) hinv hker

    exact Subtype.ext (eq_of_sub_eq_zero h0)
  ·
    intro ⟨q, hq⟩
    obtain ⟨p, hp_inv, hp_eq⟩ := cpd.Res_surjective' q hq

    exact ⟨⟨p, hp_inv⟩, Subtype.ext (by simpa [ChevalleyRestrictionPolyData.restrictionMapPoly, AlgHom.codRestrict] using hp_eq)⟩

noncomputable def chevalleyRestrictionPolynomialAlgEquiv
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m) :
    Subalgebra.invariants cpd.G cpd.G_action ≃ₐ[R]
    Subalgebra.invariants wg.W cpd.W_action :=
  AlgEquiv.ofBijective cpd.restrictionMapPoly (chevalley_restriction_polynomial cpd)

theorem chevalley_res_injective_on_invariants
    {k : Type*} [CommRing k]
    {n m : ℕ}
    (G : Type*) [Group G]
    (G_action : G →* (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k))
    (Res : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k)


    (hRes_kernel_trivial : ∀ (q : MvPolynomial (Fin n) k),
      q ∈ Subalgebra.invariants G G_action → Res q = 0 → q = 0)
    (p₁ p₂ : MvPolynomial (Fin n) k)
    (hp₁ : p₁ ∈ Subalgebra.invariants G G_action)
    (hp₂ : p₂ ∈ Subalgebra.invariants G G_action)
    (h : Res p₁ = Res p₂) :
    p₁ = p₂ := by

  have hker : Res (p₁ - p₂) = 0 := by rw [map_sub, h, sub_self]

  have hinv : (p₁ - p₂) ∈ Subalgebra.invariants G G_action := by
    intro g; simp [map_sub, hp₁ g, hp₂ g]

  have h0 := hRes_kernel_trivial (p₁ - p₂) hinv hker

  exact eq_of_sub_eq_zero h0

theorem chevalley_res_surjective_on_invariants
    {k : Type*} [Field k]
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra k 𝔤₀]
    [LieAlgebra.IsKilling k 𝔤₀] [FiniteDimensional k 𝔤₀]
    {Δ : TriangularDecomposition k 𝔤₀} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m)
    (q : MvPolynomial (Fin m) k)
    (hq : q ∈ Subalgebra.invariants wg.W cpd.W_action) :
    ∃ p : MvPolynomial (Fin n) k,
      p ∈ Subalgebra.invariants cpd.G cpd.G_action ∧ cpd.Res p = q := by


  have hbij := chevalley_restriction_polynomial cpd
  obtain ⟨⟨p, hp⟩, hpq⟩ := hbij.2 ⟨q, hq⟩
  refine ⟨p, hp, ?_⟩
  have := congr_arg Subtype.val hpq
  simpa [ChevalleyRestrictionPolyData.restrictionMapPoly, AlgHom.codRestrict] using this

theorem chevalley_restriction_theorem_10_1
    {k : Type*} [Field k]
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra k 𝔤₀]
    [LieAlgebra.IsKilling k 𝔤₀] [FiniteDimensional k 𝔤₀]
    {Δ : TriangularDecomposition k 𝔤₀} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m) :
    Function.Bijective
      ((cpd.Res.comp (Subalgebra.invariants cpd.G cpd.G_action).val).codRestrict
        (Subalgebra.invariants wg.W cpd.W_action)
        (fun ⟨x, hx⟩ => cpd.Res_maps_invariants x hx)) := by
  constructor
  ·

    intro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ heq
    have h : cpd.Res p₁ = cpd.Res p₂ := by
      have := congr_arg Subtype.val heq
      simpa [AlgHom.codRestrict] using this
    exact Subtype.ext (chevalley_res_injective_on_invariants
      cpd.G cpd.G_action cpd.Res
      cpd.kernel_trivial p₁ p₂ hp₁ hp₂ h)

  ·

    intro ⟨q, hq⟩
    obtain ⟨p, hp_inv, hp_eq⟩ := chevalley_res_surjective_on_invariants cpd q hq
    exact ⟨⟨p, hp_inv⟩, Subtype.ext (by simpa [AlgHom.codRestrict] using hp_eq)⟩

noncomputable def chevalleyRestrictionTheorem_10_1_algEquiv
    {k : Type*} [Field k]
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra k 𝔤₀]
    [LieAlgebra.IsKilling k 𝔤₀] [FiniteDimensional k 𝔤₀]
    {Δ : TriangularDecomposition k 𝔤₀} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m) :
    Subalgebra.invariants cpd.G cpd.G_action ≃ₐ[k]
    Subalgebra.invariants wg.W cpd.W_action :=
  AlgEquiv.ofBijective _ (chevalley_restriction_theorem_10_1 cpd)

noncomputable def chevalley_restriction_isomorphism
    {k : Type*} [Field k]
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra k 𝔤₀]
    [LieAlgebra.IsKilling k 𝔤₀] [FiniteDimensional k 𝔤₀]
    {Δ : TriangularDecomposition k 𝔤₀} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m) :
    Subalgebra.invariants cpd.G cpd.G_action ≃ₐ[k]
    Subalgebra.invariants wg.W cpd.W_action :=
  chevalleyRestrictionTheorem_10_1_algEquiv cpd
