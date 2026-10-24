import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section25
open CategoryTheory MonoidalCategory Limits AcyclicModels in TensorChainComplex
open AcyclicModels CategoryTheory
open AlgebraicTopology


namespace TensorChainComplex

/--
[moduleCat_free_resolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma moduleCat_free_resolution
  {R : Type}
  [CommRing R]
  [IsPrincipalIdealRing R]
  {M : ModuleCat.{0} R} :
-- imply
  Nonempty (ProjectiveResolution M) :=
-- proof
  HasProjectiveResolution.out
set_option linter.unusedSectionVars false in
/-- The Künneth decomposition isomorphism at the level of homology: for chain complexes
$C, D$ of $R$-modules over a PID $R$ with $C$ free, the homology of the tensor product
splits as a direct sum
$$H_n(C \otimes D) \;\cong\; \bigoplus_{p + q = n} H_p(C) \otimes H_q(D)
\;\oplus\; \bigoplus_{p + q = n - 1} \mathrm{Tor}_1(H_p(C), H_q(D)).$$ -/
end TensorChainComplex
namespace FreeResolutions
open CategoryTheory


namespace AcyclicModels

/--
[freeAbelianCoyoneda_map_of_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma freeAbelianCoyoneda_map_of_id
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {M X : 𝒞}
  {φ : M ⟶ X} :
-- imply
  (ConcreteCategory.hom ((freeAbelianCoyoneda M).map φ)) (FreeAbelianGroup.of (𝟙 M)) = FreeAbelianGroup.of φ := by
-- proof
  show (ConcreteCategory.hom (AddCommGrpCat.free.map ((coyoneda.obj (Opposite.op M)).map φ)))
    (FreeAbelianGroup.of (𝟙 M)) = _
  rw [AddCommGrpCat.free_map_coe]
  change FreeAbelianGroup.map ((coyoneda.obj (Opposite.op M)).map φ)
    (FreeAbelianGroup.of (𝟙 M)) = _
  rw [FreeAbelianGroup.map_of_apply]; simp [coyoneda]

end AcyclicModels

namespace AcyclicModels

/--
[freeAbelianCoyoneda_hasLiftingProperty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma freeAbelianCoyoneda_hasLiftingProperty
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {M : 𝒞}
  {G G' : 𝒞 ⥤ AddCommGrpCat.{v}}
  {η : G' ⟶ G}
  {f : freeAbelianCoyoneda M ⟶ G}
-- given
  (hM : M ∈ 𝓜)
  (hη : IsMEpi 𝓜 η) :
-- imply
  ∃ f' : freeAbelianCoyoneda M ⟶ G', f = f' ≫ η := by
-- proof
  obtain ⟨c, hc⟩ := hη M hM ((ConcreteCategory.hom (f.app M)) (FreeAbelianGroup.of (𝟙 M)))
  use liftNatTrans c
  ext X : 2; apply AddCommGrpCat.hom_ext; apply FreeAbelianGroup.lift_ext; intro φ
  simp only [NatTrans.comp_app]; dsimp [liftNatTrans]
  erw [AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of]
  have hf_nat : (ConcreteCategory.hom (f.app X)) (FreeAbelianGroup.of φ) =
    (ConcreteCategory.hom (G.map φ))
      ((ConcreteCategory.hom (f.app M)) (FreeAbelianGroup.of (𝟙 M))) := by
    have := congr_arg (fun h => (ConcreteCategory.hom h) (FreeAbelianGroup.of (𝟙 M)))
      (f.naturality φ)
    simp only [ConcreteCategory.comp_apply] at this
    rw [freeAbelianCoyoneda_map_of_id] at this; exact this
  have hη_nat : (ConcreteCategory.hom (η.app X)) ((ConcreteCategory.hom (G'.map φ)) c) =
    (ConcreteCategory.hom (G.map φ)) ((ConcreteCategory.hom (η.app M)) c) := by
    have := congr_arg (fun h => (ConcreteCategory.hom h) c) (η.naturality φ)
    simp only [ConcreteCategory.comp_apply] at this; exact this
  show (ConcreteCategory.hom (f.app X)) (FreeAbelianGroup.of φ) =
    (ConcreteCategory.hom (η.app X)) ((ConcreteCategory.hom (G'.map φ)) c)
  rw [hf_nat, hη_nat, hc]

end AcyclicModels

namespace AcyclicModels

/--
[isMFree_hasLiftingProperty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma isMFree_hasLiftingProperty
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {F : 𝒞 ⥤ AddCommGrpCat.{v}}
  {G G' : 𝒞 ⥤ AddCommGrpCat.{v}}
  {η : G' ⟶ G}
  {f : F ⟶ G}
-- given
  (hF : IsMFree 𝓜 F)
  (hη : IsMEpi 𝓜 η) :
-- imply
  ∃ f' : F ⟶ G', f = f' ≫ η := by
-- proof
  obtain ⟨ι, models, hmodels, ⟨e⟩⟩ := hF
  have hlift : ∀ i, ∃ f'_i : freeAbelianCoyoneda (models i) ⟶ G',
    Sigma.ι (fun i => freeAbelianCoyoneda (models i)) i ≫ e.inv ≫ f = f'_i ≫ η :=
    fun i => freeAbelianCoyoneda_hasLiftingProperty (hmodels i) η hη _
  choose f'_i hf'_i using hlift
  use e.hom ≫ Limits.Sigma.desc f'_i
  rw [Category.assoc]
  have hdesc_comp : Limits.Sigma.desc f'_i ≫ η =
    Limits.Sigma.desc (fun i => f'_i i ≫ η) := by
    apply Sigma.hom_ext; intro i; simp [Sigma.ι_desc_assoc, Sigma.ι_desc]
  rw [hdesc_comp]
  have hsubst : (fun i => f'_i i ≫ η) = (fun i => Sigma.ι _ i ≫ e.inv ≫ f) :=
    funext (fun i => (hf'_i i).symm)
  rw [hsubst]
  have hdesc_inv : Limits.Sigma.desc
    (fun i => Sigma.ι _ i ≫ (e.inv ≫ f)) = e.inv ≫ f := by
    apply Sigma.hom_ext; intro i; simp [Sigma.ι_desc]
  rw [hdesc_inv, Iso.hom_inv_id_assoc]

end AcyclicModels

namespace AcyclicModels

/--
[freeAbelianCoyoneda_hasLiftingProperty_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma freeAbelianCoyoneda_hasLiftingProperty_exact
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {M : 𝒞}
  {G' G G'' : 𝒞 ⥤ AddCommGrpCat.{v}}
  {η : G' ⟶ G}
  {ψ : G ⟶ G''}
  {f : freeAbelianCoyoneda M ⟶ G}
-- given
  (hM : M ∈ 𝓜)
  (hExact : IsMExact 𝓜 η ψ)
  (hf : f ≫ ψ = 0) :
-- imply
  ∃ f' : freeAbelianCoyoneda M ⟶ G', f = f' ≫ η := by
-- proof
  have hfM_ker : (ConcreteCategory.hom (ψ.app M))
    ((ConcreteCategory.hom (f.app M)) (FreeAbelianGroup.of (𝟙 M))) = 0 := by
    have := congr_arg (fun h => (ConcreteCategory.hom (h.app M)) (FreeAbelianGroup.of (𝟙 M))) hf
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
    simpa using this
  obtain ⟨_, hsurj⟩ := hExact M hM
  obtain ⟨c, hc⟩ := hsurj _ hfM_ker
  use liftNatTrans c
  ext X : 2; apply AddCommGrpCat.hom_ext; apply FreeAbelianGroup.lift_ext; intro φ
  simp only [NatTrans.comp_app]; dsimp [liftNatTrans]
  erw [AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of]
  have hf_nat : (ConcreteCategory.hom (f.app X)) (FreeAbelianGroup.of φ) =
    (ConcreteCategory.hom (G.map φ))
      ((ConcreteCategory.hom (f.app M)) (FreeAbelianGroup.of (𝟙 M))) := by
    have := congr_arg (fun h => (ConcreteCategory.hom h) (FreeAbelianGroup.of (𝟙 M)))
      (f.naturality φ)
    simp only [ConcreteCategory.comp_apply] at this
    rw [freeAbelianCoyoneda_map_of_id] at this; exact this
  have hη_nat : (ConcreteCategory.hom (η.app X)) ((ConcreteCategory.hom (G'.map φ)) c) =
    (ConcreteCategory.hom (G.map φ)) ((ConcreteCategory.hom (η.app M)) c) := by
    have := congr_arg (fun h => (ConcreteCategory.hom h) c) (η.naturality φ)
    simp only [ConcreteCategory.comp_apply] at this; exact this
  show (ConcreteCategory.hom (f.app X)) (FreeAbelianGroup.of φ) =
    (ConcreteCategory.hom (η.app X)) ((ConcreteCategory.hom (G'.map φ)) c)
  rw [hf_nat, hη_nat, hc]

end AcyclicModels

namespace AcyclicModels

/--
[isMFree_hasLiftingProperty_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma isMFree_hasLiftingProperty_exact
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {F : 𝒞 ⥤ AddCommGrpCat.{v}}
  {G' G G'' : 𝒞 ⥤ AddCommGrpCat.{v}}
  {η : G' ⟶ G}
  {ψ : G ⟶ G''}
  {f : F ⟶ G}
-- given
  (hF : IsMFree 𝓜 F)
  (hExact : IsMExact 𝓜 η ψ)
  (hf : f ≫ ψ = 0) :
-- imply
  ∃ f' : F ⟶ G', f = f' ≫ η := by
-- proof
  obtain ⟨ι, models, hmodels, ⟨e⟩⟩ := hF
  have hlift : ∀ i, ∃ f'_i : freeAbelianCoyoneda (models i) ⟶ G',
    Sigma.ι (fun i => freeAbelianCoyoneda (models i)) i ≫ e.inv ≫ f =
      f'_i ≫ η := by
    intro i
    apply freeAbelianCoyoneda_hasLiftingProperty_exact (hmodels i) η ψ hExact
    simp only [Category.assoc, hf, comp_zero]
  choose f'_i hf'_i using hlift
  use e.hom ≫ Limits.Sigma.desc f'_i
  rw [Category.assoc]
  have hdesc_comp : Limits.Sigma.desc f'_i ≫ η =
    Limits.Sigma.desc (fun i => f'_i i ≫ η) := by
    apply Sigma.hom_ext; intro i; simp [Sigma.ι_desc_assoc, Sigma.ι_desc]
  rw [hdesc_comp]
  have hsubst : (fun i => f'_i i ≫ η) = (fun i => Sigma.ι _ i ≫ e.inv ≫ f) :=
    funext (fun i => (hf'_i i).symm)
  rw [hsubst]
  have hdesc_inv : Limits.Sigma.desc
    (fun i => Sigma.ι _ i ≫ (e.inv ≫ f)) = e.inv ≫ f := by
    apply Sigma.hom_ext; intro i; simp [Sigma.ι_desc]
  rw [hdesc_inv, Iso.hom_inv_id_assoc]

end AcyclicModels

namespace AcyclicModels

/--
[IsMExactAugmented.augmentation_isMEpi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma IsMExactAugmented.augmentation_isMEpi
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {G : AugChainComplexFunctor 𝒞}
-- given
  (hG : IsMExactAugmented 𝓜 G) :
-- imply
  IsMEpi 𝓜 G.augmentation := by
-- proof
  intro M hM
  exact (hG M hM).2.1

end AcyclicModels

namespace AcyclicModels

/--
[IsMExactAugmented.dNat_isMExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma IsMExactAugmented.dNat_isMExact
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {G : AugChainComplexFunctor 𝒞}
  {n : ℕ}
-- given
  (hG : IsMExactAugmented 𝓜 G) :
-- imply
  IsMExact 𝓜 (G.dNat (n + 2) (n + 1)) (G.dNat (n + 1) n) := by
-- proof
  intro M hM
  obtain ⟨hexact, _, _⟩ := hG M hM
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  ·
    show ((G.chainFun.obj M).d (n + 1) n) ((G.chainFun.obj M).d (n + 2) (n + 1) y) = 0
    rw [← CategoryTheory.comp_apply
      ((G.chainFun.obj M).d (n + 2) (n + 1))
      ((G.chainFun.obj M).d (n + 1) n) y,
      (G.chainFun.obj M).d_comp_d (n + 2) (n + 1) n]
    simp
  ·
    have hexact_at := hexact n
    rw [HomologicalComplex.exactAt_iff' (G.chainFun.obj M)
      (n + 2) (n + 1) n
      (ChainComplex.prev ℕ (n + 1))
      (ChainComplex.next_nat_succ n)] at hexact_at
    rw [ShortComplex.ab_exact_iff] at hexact_at
    exact hexact_at x hx

end AcyclicModels

namespace AcyclicModels

/--
[IsMExactAugmented.augmentation_dNat_isMExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma IsMExactAugmented.augmentation_dNat_isMExact
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {G : AugChainComplexFunctor 𝒞}
-- given
  (hG : IsMExactAugmented 𝓜 G) :
-- imply
  IsMExact 𝓜 (G.dNat 1 0) G.augmentation := by
-- proof
  intro M hM
  obtain ⟨_, _, hcomp, hexact0⟩ := hG M hM
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  ·
    show G.augmentation.app M ((G.chainFun.obj M).d 1 0 y) = 0
    have h := CategoryTheory.comp_apply ((G.chainFun.obj M).d 1 0) (G.augmentation.app M) y
    rw [hcomp] at h
    simp at h
    exact h.symm
  ·
    exact hexact0 x hx

end AcyclicModels

/--
[AcyclicModels.acyclic_models_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma AcyclicModels.acyclic_models_existence
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {F_aug G_aug : AugChainComplexFunctor 𝒞}
  {θ : F_aug.target ⟶ G_aug.target}
-- given
  (hF_free : ∀ n : ℕ, IsMFree 𝓜 (F_aug.componentFun n))
  (hG_exact : IsMExactAugmented 𝓜 G_aug)
  (hF_d_aug : F_aug.dNat 1 0 ≫ F_aug.augmentation = 0) :
-- imply
  ∃ Φ : F_aug.chainFun ⟶ G_aug.chainFun, Covers F_aug G_aug Φ θ := by
-- proof
  obtain ⟨φ₀, hφ₀⟩ := isMFree_hasLiftingProperty (hF_free 0)
    G_aug.augmentation (hG_exact.augmentation_isMEpi) (F_aug.augmentation ≫ θ)
  have hzero1 : (F_aug.dNat 1 0 ≫ φ₀) ≫ G_aug.augmentation = 0 := by
    rw [Category.assoc, ← hφ₀, ← Category.assoc, hF_d_aug, zero_comp]
  obtain ⟨φ₁, hφ₁⟩ := isMFree_hasLiftingProperty_exact (hF_free 1)
    (G_aug.dNat 1 0) G_aug.augmentation
    hG_exact.augmentation_dNat_isMExact
    (F_aug.dNat 1 0 ≫ φ₀) hzero1
  have ind_step : ∀ (n : ℕ)
    (φ_n : F_aug.componentFun n ⟶ G_aug.componentFun n)
    (φ_np1 : F_aug.componentFun (n + 1) ⟶ G_aug.componentFun (n + 1))
    (_ : F_aug.dNat (n + 1) n ≫ φ_n = φ_np1 ≫ G_aug.dNat (n + 1) n),
    ∃ (φ_np2 : F_aug.componentFun (n + 2) ⟶ G_aug.componentFun (n + 2)),
      F_aug.dNat (n + 2) (n + 1) ≫ φ_np1 = φ_np2 ≫ G_aug.dNat (n + 2) (n + 1) := by
    intro n φ_n φ_np1 hchain
    have hzero : (F_aug.dNat (n + 2) (n + 1) ≫ φ_np1) ≫ G_aug.dNat (n + 1) n = 0 := by
      rw [Category.assoc, ← hchain, ← Category.assoc]
      have hdd : F_aug.dNat (n + 2) (n + 1) ≫ F_aug.dNat (n + 1) n = 0 := by
        ext X : 2
        simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat]
        exact (F_aug.chainFun.obj X).d_comp_d (n + 2) (n + 1) n
      rw [hdd, zero_comp]
    exact isMFree_hasLiftingProperty_exact (hF_free (n + 2))
      (G_aug.dNat (n + 2) (n + 1)) (G_aug.dNat (n + 1) n)
      (hG_exact.dNat_isMExact n)
      (F_aug.dNat (n + 2) (n + 1) ≫ φ_np1) hzero
  let ChainPair (n : ℕ) := { p : (F_aug.componentFun n ⟶ G_aug.componentFun n) ×
    (F_aug.componentFun (n + 1) ⟶ G_aug.componentFun (n + 1)) //
    F_aug.dNat (n + 1) n ≫ p.1 = p.2 ≫ G_aug.dNat (n + 1) n }
  let advance : (n : ℕ) → ChainPair n → ChainPair (n + 1) := fun n ⟨(φn, φnp1), hc⟩ =>
    ⟨(φnp1, (ind_step n φn φnp1 hc).choose), (ind_step n φn φnp1 hc).choose_spec⟩
  let base : ChainPair 0 := ⟨(φ₀, φ₁), hφ₁⟩
  let seq : (n : ℕ) → ChainPair n := fun n => Nat.rec base (fun k ih => advance k ih) n
  let φ : (n : ℕ) → (F_aug.componentFun n ⟶ G_aug.componentFun n) := fun n => (seq n).val.1
  have hshift : ∀ n, (seq (n + 1)).val.1 = (seq n).val.2 := fun n => rfl
  have hcomm : ∀ n, F_aug.dNat (n + 1) n ≫ φ n = φ (n + 1) ≫ G_aug.dNat (n + 1) n := by
    intro n
    show F_aug.dNat (n + 1) n ≫ (seq n).val.1 = (seq (n + 1)).val.1 ≫ G_aug.dNat (n + 1) n
    rw [hshift n]
    exact (seq n).property
  refine ⟨?_, ?_⟩
  · exact {
    app := fun X => {
      f := fun n => (φ n).app X
      comm' := fun i j (hij : (ComplexShape.down ℕ).Rel i j) => by
        rw [ComplexShape.down_Rel] at hij
        subst hij
        have := congr_arg (fun α => NatTrans.app α X) (hcomm j)
        simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat] at this
        exact this.symm
    }
    naturality := fun X Y f => by
      ext n : 2
      simp only [HomologicalComplex.comp_f,
        AugChainComplexFunctor.componentFun]
      exact congr_arg AddCommGrpCat.Hom.hom ((φ n).naturality f)
    }
  ·
    intro X
    show (φ 0).app X ≫ G_aug.augmentation.app X = F_aug.augmentation.app X ≫ θ.app X
    have h0 : φ 0 = φ₀ := rfl
    rw [h0]
    have := congr_arg (fun α => NatTrans.app α X) hφ₀
    simp only [NatTrans.comp_app] at this
    exact this.symm
section
open AcyclicModels CategoryTheory

/--
[AcyclicModels.acyclic_models_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma AcyclicModels.acyclic_models_uniqueness
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {F_aug G_aug : AugChainComplexFunctor 𝒞}
  {θ : F_aug.target ⟶ G_aug.target}
  {Φ₁ Φ₂ : F_aug.chainFun ⟶ G_aug.chainFun}
-- given
  (hF_free : ∀ n : ℕ, IsMFree 𝓜 (F_aug.componentFun n))
  (hG_exact : IsMExactAugmented 𝓜 G_aug)
  (hΦ₁ : Covers F_aug G_aug Φ₁ θ)
  (hΦ₂ : Covers F_aug G_aug Φ₂ θ) :
-- imply
  ObjectwiseHomotopic Φ₁ Φ₂ := by
-- proof
  let ℓ : ∀ n : ℕ, F_aug.componentFun n ⟶ G_aug.componentFun n := fun n =>
    { app := fun X => (Φ₁.app X).f n - (Φ₂.app X).f n
      naturality := fun X Y f => by
        simp only [AugChainComplexFunctor.componentFun, Functor.comp_map,
          HomologicalComplex.eval_map, Preadditive.comp_sub, Preadditive.sub_comp]
        have nat1 := congr_arg (fun α => HomologicalComplex.Hom.f α n) (Φ₁.naturality f)
        have nat2 := congr_arg (fun α => HomologicalComplex.Hom.f α n) (Φ₂.naturality f)
        simp only [HomologicalComplex.comp_f] at nat1 nat2
        exact show (F_aug.chainFun.map f).f n ≫ ((Φ₁.app Y).f n - (Φ₂.app Y).f n) =
          ((Φ₁.app X).f n - (Φ₂.app X).f n) ≫ (G_aug.chainFun.map f).f n from by
          rw [Preadditive.comp_sub, Preadditive.sub_comp, nat1, nat2] }
  have hℓ_chain : ∀ n, F_aug.dNat (n + 1) n ≫ ℓ n = ℓ (n + 1) ≫ G_aug.dNat (n + 1) n := by
    intro n
    ext X
    simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat, ℓ,
      AugChainComplexFunctor.componentFun, Functor.comp_obj, HomologicalComplex.eval_obj,
      Preadditive.comp_sub, Preadditive.sub_comp,
      (Φ₁.app X).comm' (n + 1) n rfl, (Φ₂.app X).comm' (n + 1) n rfl]
  have hℓ0_ker : ℓ 0 ≫ G_aug.augmentation = 0 := by
    ext X
    simp only [NatTrans.comp_app, ℓ, AugChainComplexFunctor.componentFun, Functor.comp_obj,
      HomologicalComplex.eval_obj, Preadditive.sub_comp, hΦ₁ X, hΦ₂ X, sub_self]
    rfl
  obtain ⟨s₀, hs₀⟩ := isMFree_hasLiftingProperty_exact (hF_free 0)
    (G_aug.dNat 1 0) G_aug.augmentation
    hG_exact.augmentation_dNat_isMExact
    (ℓ 0) hℓ0_ker
  have hzero1 : (ℓ 1 - F_aug.dNat 1 0 ≫ s₀) ≫ G_aug.dNat 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, ← hs₀, hℓ_chain 0, sub_self]
  obtain ⟨s₁, hs₁⟩ := isMFree_hasLiftingProperty_exact (hF_free 1)
    (G_aug.dNat 2 1) (G_aug.dNat 1 0)
    (hG_exact.dNat_isMExact 0)
    (ℓ 1 - F_aug.dNat 1 0 ≫ s₀) hzero1
  have advance_htpy : ∀ (n : ℕ)
    (s_n : F_aug.componentFun n ⟶ G_aug.componentFun (n + 1))
    (s_np1 : F_aug.componentFun (n + 1) ⟶ G_aug.componentFun (n + 2))
    (_ : ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ s_n = s_np1 ≫ G_aug.dNat (n + 2) (n + 1)),
    ∃ (s_np2 : F_aug.componentFun (n + 2) ⟶ G_aug.componentFun (n + 3)),
      ℓ (n + 2) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1 = s_np2 ≫ G_aug.dNat (n + 3) (n + 2) := by
    intro n s_n s_np1 hchain
    have hdd : F_aug.dNat (n + 2) (n + 1) ≫ F_aug.dNat (n + 1) n = 0 := by
      ext X : 2
      simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat]
      exact (F_aug.chainFun.obj X).d_comp_d (n + 2) (n + 1) n
    have hzero : (ℓ (n + 2) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1) ≫
      G_aug.dNat (n + 2) (n + 1) = 0 := by
      have h1 : F_aug.dNat (n + 2) (n + 1) ≫ s_np1 ≫ G_aug.dNat (n + 2) (n + 1) =
        F_aug.dNat (n + 2) (n + 1) ≫ (ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ s_n) := by
        congr 1; exact hchain.symm
      have key : (ℓ (n + 2) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1) ≫ G_aug.dNat (n + 2) (n + 1) =
        ℓ (n + 2) ≫ G_aug.dNat (n + 2) (n + 1) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1 ≫
        G_aug.dNat (n + 2) (n + 1) := by rw [Preadditive.sub_comp, Category.assoc]
      rw [key, h1, Preadditive.comp_sub, ← Category.assoc, hdd, zero_comp, sub_zero,
        ← hℓ_chain (n + 1), sub_self]
    exact isMFree_hasLiftingProperty_exact (hF_free (n + 2))
      (G_aug.dNat (n + 3) (n + 2)) (G_aug.dNat (n + 2) (n + 1))
      (hG_exact.dNat_isMExact (n + 1))
      (ℓ (n + 2) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1) hzero
  let HtpyPair (n : ℕ) := { p : (F_aug.componentFun n ⟶ G_aug.componentFun (n + 1)) ×
    (F_aug.componentFun (n + 1) ⟶ G_aug.componentFun (n + 2)) //
    ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ p.1 = p.2 ≫ G_aug.dNat (n + 2) (n + 1) }
  let advance : (n : ℕ) → HtpyPair n → HtpyPair (n + 1) := fun n ⟨(sn, snp1), hc⟩ =>
    ⟨(snp1, (advance_htpy n sn snp1 hc).choose), (advance_htpy n sn snp1 hc).choose_spec⟩
  let base : HtpyPair 0 := ⟨(s₀, s₁), hs₁⟩
  let seq : (n : ℕ) → HtpyPair n := fun n => Nat.rec base (fun k ih => advance k ih) n
  let s : (n : ℕ) → (F_aug.componentFun n ⟶ G_aug.componentFun (n + 1)) :=
    fun n => (seq n).val.1
  have hshift : ∀ n, (seq (n + 1)).val.1 = (seq n).val.2 := fun n => rfl
  have hhtpy_eq : ∀ n,
    ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ s n = s (n + 1) ≫ G_aug.dNat (n + 2) (n + 1) := by
    intro n
    show ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ (seq n).val.1 =
      (seq (n + 1)).val.1 ≫ G_aug.dNat (n + 2) (n + 1)
    rw [hshift n]
    exact (seq n).property
  have hhtpy_base : ℓ 0 = s 0 ≫ G_aug.dNat 1 0 := hs₀
  have heq : ∀ X : 𝒞, Φ₁.app X - Φ₂.app X =
    Homotopy.nullHomotopicMap' (natTransHomotopyData s X) := by
    intro X
    ext n
    cases n with
    | zero =>
      have h0 := Homotopy.nullHomotopicMap'_f_of_not_rel_left
        (k₁ := 1) (show (0 : ℕ) + 1 = 1 from rfl)
        (fun l (h : (ComplexShape.down ℕ).Rel 0 l) => by
          simp [ComplexShape.down_Rel] at h)
        (natTransHomotopyData s X)
      simp only [HomologicalComplex.sub_f_apply, h0, natTransHomotopyData]
      have h := congr_arg (fun α => NatTrans.app α X) hhtpy_base
      simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat, ℓ,
        AugChainComplexFunctor.componentFun, Functor.comp_obj,
        HomologicalComplex.eval_obj] at h
      exact congrArg (fun g => AddCommGrpCat.Hom.hom g _) h
    | succ n =>
      have hn := Homotopy.nullHomotopicMap'_f
        (k₂ := n + 2) (k₀ := n)
        (show (n + 1 : ℕ) + 1 = n + 2 from rfl)
        (show n + 1 = n + 1 from rfl)
        (natTransHomotopyData s X)
      simp only [HomologicalComplex.sub_f_apply, hn, natTransHomotopyData]
      have heq_n := congr_arg (fun α => NatTrans.app α X) (hhtpy_eq n)
      simp only [NatTrans.comp_app, NatTrans.app_sub, AugChainComplexFunctor.dNat, ℓ,
        AugChainComplexFunctor.componentFun, Functor.comp_obj,
        HomologicalComplex.eval_obj] at heq_n
      have h := eq_add_of_sub_eq heq_n
      simp only [NatTrans.comp_app] at h
      conv at h => rhs; rw [add_comm]
      exact congrArg (fun g => AddCommGrpCat.Hom.hom g _) h
  intro X
  exact ⟨natTransHomotopy Φ₁ Φ₂ s heq X⟩
end

/--
[AcyclicModels.acyclic_models](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean)
-/
@[path]
lemma AcyclicModels.acyclic_models
  {𝒞 : Type u}
  [Category.{v} 𝒞]
  {𝓜 : Set 𝒞}
  {F_aug G_aug : AugChainComplexFunctor 𝒞}
  {θ : F_aug.target ⟶ G_aug.target}
-- given
  (hF_free : ∀ n : ℕ, IsMFree 𝓜 (F_aug.componentFun n))
  (hG_exact : IsMExactAugmented 𝓜 G_aug)
  (hF_d_aug : F_aug.dNat 1 0 ≫ F_aug.augmentation = 0) :
-- imply
  (∃ Φ : F_aug.chainFun ⟶ G_aug.chainFun, Covers F_aug G_aug Φ θ) ∧ (∀ Φ₁ Φ₂ : F_aug.chainFun ⟶ G_aug.chainFun, Covers F_aug G_aug Φ₁ θ → Covers F_aug G_aug Φ₂ θ → ObjectwiseHomotopic Φ₁ Φ₂) :=
-- proof
  ⟨acyclic_models_existence 𝓜 F_aug G_aug θ hF_free hG_exact hF_d_aug,
    fun Φ₁ Φ₂ hΦ₁ hΦ₂ => acyclic_models_uniqueness 𝓜 F_aug G_aug θ hF_free hG_exact Φ₁ Φ₂ hΦ₁ hΦ₂⟩
namespace KunnethTopological
open AlgebraicTopology
variable (R : Type) [CommRing R]


-- created on 2026-10-23
