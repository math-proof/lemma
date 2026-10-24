/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section34
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Cofinal
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open Set

namespace CechCohomology

/-- A map `φ : J → I` between preorders is **cofinal** if every `i : I` is
$\le$ some `φ j`. Used to recognise when pulling a directed system back along
`φ` gives the same direct limit. -/
def IsCofinalMap {I : Type*} {J : Type*} [LE I] (φ : J → I) : Prop :=
  ∀ i : I, ∃ j : J, i ≤ φ j

section DirectLimits

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [DecidableEq κ] [Nonempty κ]
variable (G : ι → Type*) [∀ i, AddCommGroup (G i)]
variable (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G fun i j h ↦ f i j h]
variable (φ : κ →o ι)

/-- Pullback of the bonding maps of a directed system `(G, f)` along a monotone
map `φ : κ →o ι`: the pulled-back system has fibres `G (φ j)` and bonding maps
`f (φ j₁) (φ j₂) (φ.monotone h)`. -/
def pullbackBondingMap (j₁ j₂ : κ) (h : j₁ ≤ j₂) : G (φ j₁) →+ G (φ j₂) :=
  f (φ j₁) (φ j₂) (φ.monotone h)

/-- The canonical map from the direct limit of the pulled-back system over `κ`
to the direct limit over `ι` of the original system, induced by the universal
property of direct limits. -/
noncomputable def cofinalMap :
    AddCommGroup.DirectLimit (fun j => G (φ j)) (pullbackBondingMap G f φ) →+
    AddCommGroup.DirectLimit G f :=
  AddCommGroup.DirectLimit.lift _ _ _
    (fun j => AddCommGroup.DirectLimit.of G f (φ j))
    (fun _ _ hij x => AddCommGroup.DirectLimit.of_f (f := f) (φ.monotone hij) x)

/-- **Lemma 35.7 (cofinal maps and direct limits).** If `φ : κ →o ι` is cofinal
(every `i : ι` is `≤ φ j` for some `j : κ`), then the induced map between
direct limits is an additive equivalence: the limit over a cofinal subset
recovers the full limit. -/
noncomputable def cofinalMapEquiv
    (hcof : ∀ i : ι, ∃ j : κ, i ≤ φ j) :
    AddCommGroup.DirectLimit (fun j => G (φ j)) (pullbackBondingMap G f φ) ≃+
    AddCommGroup.DirectLimit G f :=
  AddEquiv.ofBijective (cofinalMap G f φ)
    ⟨by


      rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [AddMonoidHom.mem_ker] at ha
      induction a using AddCommGroup.DirectLimit.induction_on with
      | ih j x =>
        simp only [cofinalMap, AddCommGroup.DirectLimit.lift_of] at ha
        obtain ⟨i, hji, hzero⟩ := AddCommGroup.DirectLimit.of.zero_exact (φ j) x ha
        obtain ⟨j', hij'⟩ := hcof i
        obtain ⟨k, hjk, hj'k⟩ := directed_of (· ≤ ·) j j'
        have h_i_phik : i ≤ φ k := le_trans hij' (φ.monotone hj'k)
        have key : pullbackBondingMap G f φ j k hjk x = 0 := by
          show f (φ j) (φ k) (φ.monotone hjk) x = 0
          rw [show f (φ j) (φ k) (φ.monotone hjk) x =
                f i (φ k) h_i_phik (f (φ j) i hji x) from
            (DirectedSystem.map_map (f := fun i j h ↦ f i j h) hji h_i_phik x).symm]
          rw [hzero, map_zero]
        simp only [AddSubgroup.mem_bot]
        rw [show AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) j x =
          AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) k
            (pullbackBondingMap G f φ j k hjk x)
          from (AddCommGroup.DirectLimit.of_f (f := pullbackBondingMap G f φ) hjk x).symm]
        rw [key, map_zero],
    by
      intro a
      induction a using AddCommGroup.DirectLimit.induction_on with
      | ih i x =>
        obtain ⟨j, hij⟩ := hcof i
        exact ⟨AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) j
          (f i (φ j) hij x), by
          simp only [cofinalMap, AddCommGroup.DirectLimit.lift_of]
          exact AddCommGroup.DirectLimit.of_f (f := f) hij x⟩⟩

end DirectLimits

variable {X : Type*} [TopologicalSpace X]

/-- The functor sending a space `Y` to its integral singular chain complex
$S_\bullet(Y; \mathbb{Z})$ as a chain complex of `ℤ`-modules. -/
abbrev singChain : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- $p$-th integral singular cohomology $H^p(Y; \mathbb{Z})$ of a space `Y`,
computed by dualising `singChain Y` and taking the `p`-th cohomology. -/
def singCohom (Y : TopCat.{0}) (p : ℕ) : ModuleCat.{0} ℤ :=
  ((singChain.obj Y).linearYonedaObj ℤ (ModuleCat.of ℤ ℤ)).homology p

end CechCohomology

/-- Čech cohomology $\check{H}^p(X, K; \mathbb{Z})$ of a subset `K ⊆ X`,
defined as the direct limit (`cechCohomology`) of singular cohomology over
open neighborhoods of `K`. -/
def CechCohomology.CechCohom
    (X : Type) [TopologicalSpace X] (K : Set X) (p : ℕ) : Type :=
  (CechCohomology.cechCohomology ℤ K p : Type)

/-- The additive group structure on `CechCohom X K p`, inherited from the
underlying module. -/
noncomputable instance CechCohomology.CechCohom.addCommGroup
    (X : Type) [TopologicalSpace X]
    (K : Set X) (p : ℕ) : AddCommGroup (CechCohomology.CechCohom X K p) :=
  (CechCohomology.cechCohomology ℤ K p).isAddCommGroup


/-- The restriction homomorphism $\check{H}^p(X, K) \to \check{H}^p(X, L)$ for
$L \subseteq K$, induced functorially by precomposition with open
neighborhoods. -/
namespace CechCohomology

open CechCohomology Function

/-- Mayer–Vietoris restriction map: a class on `A ∪ B` restricts to a pair of
classes on `A` and `B`. -/
end CechCohomology

namespace CechCohomology

open TopologicalSpace SingularCohomology CategoryTheory

/-- A **relative neighborhood pair** for `L ⊆ K ⊆ X`: a pair of open sets
`U ⊇ K`, `V ⊇ L` with `V ≤ U`. The directed system indexed by these pairs is
used to define relative Čech cohomology. -/
structure RelNbhdPair {X : Type} [TopologicalSpace X] (K L : Set X) where
  U : Opens X
  V : Opens X
  hK : K ⊆ ↑U
  hL : L ⊆ ↑V
  hVU : V ≤ U

variable {X : Type} [TopologicalSpace X]

/-- Preorder on relative neighborhood pairs: `p ≤ q` iff `q.U ⊆ p.U` and
`q.V ⊆ p.V` (smaller neighborhoods correspond to larger elements). -/
instance relNbhdPair_preorder {K L : Set X} : Preorder (RelNbhdPair K L) where
  le p q := q.U ≤ p.U ∧ q.V ≤ p.V
  le_refl _ := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ hpq hqr := ⟨le_trans hqr.1 hpq.1, le_trans hqr.2 hpq.2⟩

/-- The preorder of relative neighborhood pairs is directed: any two pairs
admit a common refinement obtained by intersecting their components. -/
instance relNbhdPair_directed {K L : Set X} :
    IsDirected (RelNbhdPair K L) (· ≤ ·) where
  directed p q := ⟨⟨p.U ⊓ q.U, p.V ⊓ q.V,
    fun _ hx => ⟨p.hK hx, q.hK hx⟩,
    fun _ hx => ⟨p.hL hx, q.hL hx⟩,
    inf_le_inf p.hVU q.hVU⟩,
    ⟨inf_le_left, inf_le_left⟩, ⟨inf_le_right, inf_le_right⟩⟩

/-- The preorder of relative neighborhood pairs is nonempty: the pair
`(⊤, ⊤)` (the whole space, the whole space) is always a valid neighborhood
pair. -/
instance relNbhdPair_nonempty {K L : Set X} : Nonempty (RelNbhdPair K L) :=
  ⟨⟨⊤, ⊤, fun _ _ => trivial, fun _ _ => trivial, le_refl _⟩⟩

/-- Continuous inclusion $V \hookrightarrow U$ associated to a relative
neighborhood pair `(U, V)`, viewed as a morphism in `TopCat`. -/
def relNbhdInclusion {K L : Set X} (pair : RelNbhdPair K L) :
    TopCat.of ↑pair.V.1 ⟶ TopCat.of ↑pair.U.1 :=
  ⟨fun x => ⟨x.1, pair.hVU x.2⟩, continuous_inclusion pair.hVU⟩

/-- Relative singular cohomology $H^p(U, V; \mathbb{Z})$ of the pair of open
sets `(U, V)` associated to a relative neighborhood pair. -/
noncomputable def relSingCohomOfPair {K L : Set X}
    (pair : RelNbhdPair K L) (p : ℕ) : ModuleCat.{0} ℤ :=
  relativeSingularCohomology ℤ (TopCat.of ↑pair.U.1) (TopCat.of ↑pair.V.1)
    (relNbhdInclusion pair) (ModuleCat.of ℤ ℤ) p

/-- Index-wise family $\mathrm{pair} \mapsto H^p(U_{\mathrm{pair}}, V_{\mathrm{pair}})$
whose direct limit will define relative Čech cohomology. -/
def relCechFam (K L : Set X) (p : ℕ) (pair : RelNbhdPair K L) : Type :=
  (relSingCohomOfPair pair p : Type _)

/-- The additive group structure on each fibre of `relCechFam`. -/
noncomputable instance relCechFam_addCommGroup {K L : Set X}
    (p : ℕ) (pair : RelNbhdPair K L) :
    AddCommGroup (relCechFam K L p pair) :=
  (relSingCohomOfPair pair p).isAddCommGroup

/-- Continuous inclusion `U₂ ↪ U₁` of opens (with `U₂ ≤ U₁`) viewed as a
morphism in `TopCat`. -/
def opensInclusion {U₁ U₂ : Opens X} (h : U₂ ≤ U₁) :
    TopCat.of ↑U₂.1 ⟶ TopCat.of ↑U₁.1 :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- Naturality square for opens inclusions: the two ways of composing the
inclusions $V_2 \hookrightarrow V_1 \hookrightarrow U_1$ and
$V_2 \hookrightarrow U_2 \hookrightarrow U_1$ agree. -/
theorem opensInclusion_comm {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    opensInclusion h.2 ≫ relNbhdInclusion pair₁ =
    relNbhdInclusion pair₂ ≫ opensInclusion h.1 := by
  apply TopCat.ext
  intro x
  rfl

/-- The cochain-restriction operation is contravariantly functorial in
composition of continuous maps. -/
theorem restrictionCochainMap_comp (R : Type) [CommRing R]
    (G : ModuleCat.{0} R) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrictionCochainMap R G (f ≫ g) =
    restrictionCochainMap R G g ≫ restrictionCochainMap R G f := by
  simp only [restrictionCochainMap, Functor.map_comp]
  rfl

/-- Commutativity of restriction cochain maps along the square of inclusions
associated to `pair₁ ≤ pair₂`: derives from `opensInclusion_comm` and the
contravariant functoriality of restriction. -/
theorem restrictionCochainMap_square {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ≫
      restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2) =
    restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1) ≫
      restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) := by
  rw [← restrictionCochainMap_comp, ← restrictionCochainMap_comp,
      opensInclusion_comm pair₁ pair₂ h]

open CategoryTheory.Limits in
/-- Transition map of relative singular cochain complexes induced by
`pair₁ ≤ pair₂`: the canonical map between kernels of the restriction cochain
maps coming from the commuting square. -/
noncomputable def relCochainComplexMap {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relativeSingularCochainComplex ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ⟶
    relativeSingularCochainComplex ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) :=
  kernel.map
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2))
    (restrictionCochainMap_square pair₁ pair₂ h)

/-- Transition map between relative singular cohomology groups
$H^p(U_1, V_1) \to H^p(U_2, V_2)$ for `pair₁ ≤ pair₂`, obtained by taking
$p$-th homology of `relCochainComplexMap`. -/
noncomputable def relCohomTransitionModMap {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) (p : ℕ) :
    relSingCohomOfPair pair₁ p ⟶ relSingCohomOfPair pair₂ p :=
  HomologicalComplex.homologyMap (relCochainComplexMap pair₁ pair₂ h) p

/-- Bonding map of the directed system `relCechFam K L p`: the underlying
additive group hom of `relCohomTransitionModMap`. -/
noncomputable def relCechTransitionMap
    {K L : Set X}
    (p : ℕ) (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relCechFam K L p pair₁ →+ relCechFam K L p pair₂ :=
  (relCohomTransitionModMap pair₁ pair₂ h p).hom.toAddMonoidHom

end CechCohomology


open CategoryTheory CategoryTheory.Limits SingularCohomology in
/-- `relCechFam K L p` together with `relCechTransitionMap` is a directed
system: identities act as identities, and composition of bondings respects
composition of inclusions. -/
noncomputable instance CechCohomology.relCechFam_directedSystem_axioms
    {X : Type} [TopologicalSpace X] {K L : Set X} (p : ℕ) :
    DirectedSystem (CechCohomology.relCechFam K L p)
      (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h) where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap (CechCohomology.relCochainComplexMap i i (le_refl i)) p).hom.toAddMonoidHom x = x
    have hid1 : CechCohomology.opensInclusion (le_refl i).1 =
        𝟙 (TopCat.of ↑i.U.1) := by apply TopCat.ext; intro x; rfl
    have hres1 : restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.U.1)) = 𝟙 _ := by
      simp only [restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    have hrelMap : CechCohomology.relCochainComplexMap i i (le_refl i) = 𝟙 _ := by
      unfold CechCohomology.relCochainComplexMap relativeSingularCochainComplex
      rw [← cancel_mono (kernel.ι (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i)))]
      simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
      rw [hid1]
      simp only [hres1, Category.comp_id]
    rw [hrelMap, HomologicalComplex.homologyMap_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    simp only [CechCohomology.relCechTransitionMap, CechCohomology.relCohomTransitionModMap]
    have hcomp1 : CechCohomology.opensInclusion hjk.1 ≫ CechCohomology.opensInclusion hij.1 =
        CechCohomology.opensInclusion (hij.trans hjk).1 := by
      apply TopCat.ext; intro x; rfl
    have hrelComp : CechCohomology.relCochainComplexMap i j hij ≫
        CechCohomology.relCochainComplexMap j k hjk =
        CechCohomology.relCochainComplexMap i k (hij.trans hjk) := by
      unfold CechCohomology.relCochainComplexMap relativeSingularCochainComplex
      rw [← cancel_mono (kernel.ι (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion k)))]
      simp only [Category.assoc, kernel.lift_ι]
      rw [kernel.lift_ι_assoc]
      simp only [Category.assoc, kernel.lift_ι]
      congr 1
      rw [← CechCohomology.restrictionCochainMap_comp, hcomp1]
    rw [show CechCohomology.relCochainComplexMap i k (hij.trans hjk) =
      CechCohomology.relCochainComplexMap i j hij ≫
      CechCohomology.relCochainComplexMap j k hjk from hrelComp.symm]
    rw [HomologicalComplex.homologyMap_comp]
    rfl

namespace CechCohomology

variable {X : Type} [TopologicalSpace X]

/-- Convenience instance form of `relCechFam_directedSystem_axioms`. -/
instance relCechFam_directedSystem {K L : Set X} (p : ℕ) :
    DirectedSystem (relCechFam K L p)
      (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h) :=
  relCechFam_directedSystem_axioms p

/-- **Relative Čech cohomology** $\check{H}^p(X, K, L)$: the direct limit over
relative neighborhood pairs of `(K, L)` of the relative singular cohomology
$H^p(U, V; \mathbb{Z})$. -/
noncomputable def CechCohomRel
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) : Type :=
  open Classical in
  AddCommGroup.DirectLimit (relCechFam K L p)
    (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)

namespace CechCohomRel

/-- Additive group structure on `CechCohomRel X K L p` from the direct limit. -/
noncomputable instance addCommGroup
    (X : Type) [TopologicalSpace X]
    (K L : Set X) (p : ℕ) : AddCommGroup (CechCohomRel X K L p) :=
  open Classical in
  AddCommGroup.DirectLimit.addCommGroup _ _

end CechCohomRel
end CechCohomology

/-- Restriction of a relative neighborhood pair along inclusions `L₁ ⊆ K₁`,
`L₂ ⊆ K₂`: a neighborhood pair of `(K₁, K₂)` is also one of `(L₁, L₂)`. -/
class that vanishes under restriction was already zero. -/
namespace CechCohomology

/-- Bijectivity form of excision (normal case): for closed `A`, `B` in a
normal Hausdorff space, the inclusion
$(B, A \cap B) \hookrightarrow (A \cup B, A)$ induces a bijection on relative
Čech cohomology. -/
end CechCohomology


/-- Bijectivity form of excision (compact case): for compact `A`, `B` in a
Hausdorff space, the inclusion-induced map on relative Čech cohomology is
bijective. -/
def CechCohomology.lesIndexType
    (X : Type) [TopologicalSpace X] (K L : Set X) : Type :=
  CechCohomology.RelNbhdPair K L

/-- Preorder on the LES index type, inherited from `relNbhdPair_preorder`. -/
instance CechCohomology.lesIndexPreorder
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    Preorder (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_preorder

/-- Directedness of the LES index type. -/
instance CechCohomology.lesIndexDirected
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    IsDirectedOrder (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_directed

/-- Classical decidable equality on the LES index type. -/
noncomputable instance CechCohomology.lesIndexDecEq
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    DecidableEq (CechCohomology.lesIndexType X K L) :=
  open Classical in inferInstance

/-- Nonemptiness of the LES index type. -/
instance CechCohomology.lesIndexNonempty
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    Nonempty (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_nonempty

/-- Relative cohomology family $i \mapsto H^p(U_i, V_i)$ for the pointwise
long exact sequence. -/
def CechCohomology.relFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  CechCohomology.relCechFam K L p

/-- Additive group structure on each fibre of `relFamily`. -/
noncomputable instance CechCohomology.relFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.relFamily X K L p i) :=
  CechCohomology.relCechFam_addCommGroup p i

/-- Absolute cohomology family $i \mapsto H^p(U_i)$ — middle term of the
pointwise LES. -/
def CechCohomology.absKFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  fun i => (CechCohomology.singCohom (TopCat.of ↑i.U.1) p : Type)

/-- Additive group structure on each fibre of `absKFamily`. -/
noncomputable instance CechCohomology.absKFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.absKFamily X K L p i) :=
  (CechCohomology.singCohom (TopCat.of ↑i.U.1) p).isAddCommGroup

/-- Absolute cohomology family $i \mapsto H^p(V_i)$ — third term of the
pointwise LES. -/
def CechCohomology.absLFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  fun i => (CechCohomology.singCohom (TopCat.of ↑i.V.1) p : Type)

/-- Additive group structure on each fibre of `absLFamily`. -/
noncomputable instance CechCohomology.absLFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.absLFamily X K L p i) :=
  (CechCohomology.singCohom (TopCat.of ↑i.V.1) p).isAddCommGroup

/-- Bonding map for the relative cohomology directed system; re-export of
`relCechTransitionMap`. -/
noncomputable def CechCohomology.relBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.relFamily X K L p i →+ CechCohomology.relFamily X K L p j :=
  CechCohomology.relCechTransitionMap p i j h

/-- `relFamily` together with `relBond` is a directed system. -/
noncomputable instance CechCohomology.relBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.relFamily X K L p)
      fun i j h => CechCohomology.relBond X K L p i j h :=
  CechCohomology.relCechFam_directedSystem_axioms p

/-- Bonding map for `absKFamily`: pullback of singular cohomology along the
open inclusion $U_j \hookrightarrow U_i$. -/
noncomputable def CechCohomology.absKBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.absKFamily X K L p i →+ CechCohomology.absKFamily X K L p j :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom


/-- `absKFamily` together with `absKBond` is a directed system. -/
noncomputable instance CechCohomology.absKBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.absKFamily X K L p)
      fun i j h => CechCohomology.absKBond X K L p i j h where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_refl i.U))) p).hom.toAddMonoidHom x = x
    have hid : CechCohomology.opensInclusion (le_refl i.U) =
        𝟙 (TopCat.of ↑i.U.1) := by apply TopCat.ext; intro x; rfl
    have hres : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.U.1)) = 𝟙 _ := by
      simp only [SingularCohomology.restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hres, HomologicalComplex.homologyMap_id]
    simp
  map_map := by
    intro k j i hij hjk x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.1)) p).hom.toAddMonoidHom
      ((HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion hij.1)) p).hom.toAddMonoidHom x) =
      (HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion (le_trans hjk.1 hij.1))) p).hom.toAddMonoidHom x
    have hcomp : CechCohomology.opensInclusion hjk.1 ≫ CechCohomology.opensInclusion hij.1 =
        CechCohomology.opensInclusion (le_trans hjk.1 hij.1) := by
      apply TopCat.ext; intro x; rfl
    rw [show SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_trans hjk.1 hij.1)) =
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hij.1) ≫
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.1)
      from by rw [← CechCohomology.restrictionCochainMap_comp, hcomp]]
    rw [HomologicalComplex.homologyMap_comp]
    simp [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp]

/-- Bonding map for `absLFamily`: pullback of singular cohomology along the
open inclusion $V_j \hookrightarrow V_i$. -/
noncomputable def CechCohomology.absLBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.absLFamily X K L p i →+ CechCohomology.absLFamily X K L p j :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.2)) p).hom.toAddMonoidHom


/-- `absLFamily` together with `absLBond` is a directed system. -/
noncomputable instance CechCohomology.absLBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.absLFamily X K L p)
      fun i j h => CechCohomology.absLBond X K L p i j h where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_refl i.V))) p).hom.toAddMonoidHom x = x
    have hid : CechCohomology.opensInclusion (le_refl i.V) =
        𝟙 (TopCat.of ↑i.V.1) := by apply TopCat.ext; intro x; rfl
    have hres : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.V.1)) = 𝟙 _ := by
      simp only [SingularCohomology.restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hres, HomologicalComplex.homologyMap_id]
    simp
  map_map := by
    intro k j i hij hjk x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.2)) p).hom.toAddMonoidHom
      ((HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion hij.2)) p).hom.toAddMonoidHom x) =
      (HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion (le_trans hjk.2 hij.2))) p).hom.toAddMonoidHom x
    have hcomp : CechCohomology.opensInclusion hjk.2 ≫ CechCohomology.opensInclusion hij.2 =
        CechCohomology.opensInclusion (le_trans hjk.2 hij.2) := by
      apply TopCat.ext; intro x; rfl
    rw [show SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_trans hjk.2 hij.2)) =
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hij.2) ≫
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.2)
      from by rw [← CechCohomology.restrictionCochainMap_comp, hcomp]]
    rw [HomologicalComplex.homologyMap_comp]
    simp [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp]


/-- Pointwise rel-to-abs map at a single neighborhood pair `i = (U, V)`:
$H^p(U, V) \to H^p(U)$, from the kernel inclusion. -/
noncomputable def CechCohomology.ptRelToAbs
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.relFamily X K L p i →+ CechCohomology.absKFamily X K L p i :=
  (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i))) p).hom.toAddMonoidHom

/-- Pointwise restriction map at `i = (U, V)`: $H^p(U) \to H^p(V)$, induced by
pullback along the inclusion $V \hookrightarrow U$. -/
noncomputable def CechCohomology.ptRestrict
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.absKFamily X K L p i →+ CechCohomology.absLFamily X K L p i :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i)) p).hom.toAddMonoidHom


/-- The restriction-of-cochains map associated to a relative neighborhood pair
is an epimorphism in the category of cochain complexes of `ℤ`-modules. -/
noncomputable def CechCohomology.cochainSES
    {X : Type} [TopologicalSpace X] {K L : Set X}
    (i : CechCohomology.lesIndexType X K L) :
    (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i)))
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i))
      (CategoryTheory.Limits.kernel.condition _)).ShortExact := by
  letI : CategoryTheory.Abelian (CochainComplex (ModuleCat.{0} ℤ) ℕ) := inferInstance
  exact CategoryTheory.ShortComplex.ShortExact.mk
    (CategoryTheory.ShortComplex.exact_of_f_is_kernel _
      (CategoryTheory.Limits.kernelIsKernel _))

/-- Pointwise connecting homomorphism $H^p(V) \to H^{p+1}(U, V)$ associated to
`cochainSES i`. -/
noncomputable def CechCohomology.ptConnecting
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.absLFamily X K L p i →+ CechCohomology.relFamily X K L (p + 1) i :=
  ((CechCohomology.cochainSES i).δ p (p + 1) rfl).hom.toAddMonoidHom


/-- Definitional identification of `CechCohomRel X K L p` with the direct limit
of `relFamily`. -/
noncomputable def CechCohomology.eqvRel
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.CechCohomRel X K L p ≃+
    AddCommGroup.DirectLimit (CechCohomology.relFamily X K L p)
      (CechCohomology.relBond X K L p) :=
  AddEquiv.refl _


/-- Identification of $\check{H}^p(X, K)$ with the direct limit of `absKFamily`
over relative neighborhood pairs of `(K, L)`: the neighborhoods `U_i` of `K`
appearing as the first component of `RelNbhdPair K L` are cofinal among all
open neighborhoods of `K`. -/
namespace CechCohomology

open Function


/-- **Theorem 35.2 (Long exact sequence of a pair in Čech cohomology).** For
closed $L \subseteq K \subseteq X$, the sequence
$\cdots \to \check{H}^p(X, K, L) \to \check{H}^p(X, K) \to \check{H}^p(X, L)
\to \check{H}^{p+1}(X, K, L) \to \cdots$
is exact. Proved by combining the pointwise short-exact sequences of
neighborhood pairs with `addCommGroup_directLimit_map_exact` and transporting
along the equivalences `eqvRel`, `eqvAbsK`, `eqvAbsL`. -/
