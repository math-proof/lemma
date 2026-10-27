import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI CWComplex CWComplex.SkeletonHomology CWHomology CellularHomology
open Topology


namespace CWComplex.SkeletonHomology

/--
[skeletonInclusion_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeletonInclusion_factor
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k : ℕ} :
-- imply
  skeletonInclusion X k = skeletonStepInclusion X k ≫ skeletonInclusion X (k + 1) := by
-- proof
  ext x; rfl

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[skeletonHomologyMap_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeletonHomologyMap_factor
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {q k : ℕ} :
-- imply
  skeletonHomologyMap X q k = skeletonStepHomologyMap X q k ≫ skeletonHomologyMap X q (k + 1) := by
-- proof
  show ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
    (skeletonInclusion X k) =
    ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
      (skeletonStepInclusion X k) ≫
    ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
      (skeletonInclusion X (k + 1))
  rw [← Functor.map_comp, ← skeletonInclusion_factor]
end CWComplex.SkeletonHomology
namespace CWComplex.SkeletonHomology

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[skeleton_zero_inter_openCell_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeleton_zero_inter_openCell_empty
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {n : ℕ}
  {j : Topology.RelCWComplex.cell (Set.univ : Set X) n}
-- given
  (hn : n ≥ 1) :
-- imply
  (CWComplex.skeleton X 0 : Set X) ∩ Topology.RelCWComplex.openCell n j = ∅ := by
-- proof
  have hni : j ∉ (CWComplex.skeleton X 0 : Topology.RelCWComplex.Subcomplex _).I n := by
    simp only [CWComplex.skeleton, Topology.RelCWComplex.skeletonLT,
      Topology.RelCWComplex.Subcomplex.mk', Set.mem_setOf_eq]
    push Not
    exact_mod_cast hn
  have := Topology.RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem
    (CWComplex.skeleton X 0 : Topology.RelCWComplex.Subcomplex _) hni
  rw [Set.disjoint_iff_inter_eq_empty] at this
  rw [Set.inter_comm]; exact this

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[skeleton_zero_inter_closedCell_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeleton_zero_inter_closedCell_finite
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)] :
-- imply
  ∀ (n : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set X) n), Set.Finite ((CWComplex.skeleton X 0 : Set X) ∩ Topology.RelCWComplex.closedCell n j) := by
-- proof
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j
    by_cases hn : n = 0
    · subst hn
      have : Topology.RelCWComplex.closedCell (C := Set.univ) 0 j =
        {(Topology.RelCWComplex.map (C := Set.univ) 0 j : PartialEquiv (Fin 0 → ℝ) X)
          default} := by
        ext y
        simp only [Topology.RelCWComplex.closedCell, Set.mem_image, Metric.mem_closedBall,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨z, _, rfl⟩
          congr 1
          exact Subsingleton.elim z default
        · rintro rfl
          exact ⟨default, by simp [Subsingleton.elim (default : Fin 0 → ℝ) 0], rfl⟩
      rw [this]
      exact Set.Finite.subset (Set.finite_singleton _) Set.inter_subset_right
    · have hn1 : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
      rw [Set.inter_union_distrib_left]
      apply Set.Finite.union
      · obtain ⟨I, hI⟩ := Topology.CWComplex.cellFrontier_subset_finite_closedCell
        (C := Set.univ) n j
        apply Set.Finite.subset _ (Set.inter_subset_inter_right _ hI)
        rw [Set.inter_iUnion₂]
        apply Set.Finite.biUnion
          ((Set.finite_Iio n).subset fun _ hm => hm)
        intro m hm
        rw [Set.inter_iUnion₂]
        apply Set.Finite.biUnion (I m).finite_toSet
        intro j' _
        exact ih m hm j'
      · rw [skeleton_zero_inter_openCell_empty hn1 j]
        exact Set.finite_empty

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[isClosed_subset_skeleton_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma isClosed_subset_skeleton_zero
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {A : Set X}
-- given
  (hA : A ⊆ (CWComplex.skeleton X 0 : Set X)) :
-- imply
  IsClosed A := by
-- proof
  apply Topology.CWComplex.closed' A (Set.subset_univ A)
  intro n j
  exact (Set.Finite.subset (skeleton_zero_inter_closedCell_finite n j)
    (Set.inter_subset_inter_left _ hA)).isClosed

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[skeleton_zero_totallyDisconnected](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeleton_zero_totallyDisconnected
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)] :
-- imply
  TotallyDisconnectedSpace ↥(CWComplex.skeleton X 0 : Set X) := by
-- proof
  have : DiscreteTopology ↥(CWComplex.skeleton X 0 : Set X) := by
    rw [discreteTopology_iff_forall_isClosed]
    intro s
    rw [isClosed_induced_iff]
    refine ⟨Subtype.val '' s, ?_, ?_⟩
    · apply isClosed_subset_skeleton_zero
      intro x hx
      obtain ⟨⟨y, hy⟩, _, hyx⟩ := hx
      rw [← hyx]; exact hy
    · ext ⟨x, hx⟩
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨⟨y, hy⟩, hys, hyx⟩
        have : (⟨y, hy⟩ : ↥(CWComplex.skeleton X 0 : Set X)) = ⟨x, hx⟩ :=
          Subtype.ext hyx
        rwa [this] at hys
      · intro hxs
        exact ⟨⟨x, hx⟩, hxs, rfl⟩
  infer_instance
end CWComplex.SkeletonHomology
namespace CWComplex.SkeletonHomology

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[les_pair_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma les_pair_isZero
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {q k : ℕ}
-- given
  (hk : IsZero (SingularHomologyGroup q ↥(CWComplex.skeleton X k : Set X)))
  (hrel : IsZero (Excision.RelativeSingularHomologyGroup q ↥(CWComplex.skeleton X (k + 1) : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)))) :
-- imply
  IsZero (SingularHomologyGroup q ↥(CWComplex.skeleton X (k + 1) : Set X)) := by
-- proof
  let Y : Type := ↥(CWComplex.skeleton X (k + 1) : Set X)
  let A : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)
  have hse := Excision.bottomSES_shortExact Y A
  have hexact := hse.homology_exact₂ q
  have hrel' : IsZero ((Excision.bottomSES Y A).X₃.homology q) := hrel
  have hg_zero : HomologicalComplex.homologyMap (Excision.bottomSES Y A).g q = 0 :=
    hrel'.eq_of_tgt _ _
  have hA_homeo : ↥A ≃ₜ ↥(CWComplex.skeleton X k : Set X) :=
    { toEquiv := {
      toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
        (by norm_cast; omega) hx⟩, hx⟩
      left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
      right_inv := fun ⟨x, _⟩ => rfl }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  have hA_iso : TopCat.of ↥A ≅ TopCat.of ↥(CWComplex.skeleton X k : Set X) :=
    TopCat.isoOfHomeo hA_homeo
  have hchain_iso : Excision.singularChainZ.obj (TopCat.of ↥A) ≅
    Excision.singularChainZ.obj (TopCat.of ↥(CWComplex.skeleton X k : Set X)) :=
    Excision.singularChainZ.mapIso hA_iso
  have hhom_iso : (Excision.bottomSES Y A).X₁.homology q ≅
    SingularHomologyGroup q ↥(CWComplex.skeleton X k : Set X) :=
    (HomologicalComplex.homologyFunctor _ _ q).mapIso hchain_iso
  have hA_zero : IsZero ((Excision.bottomSES Y A).X₁.homology q) :=
    hk.of_iso hhom_iso
  have hf_zero : HomologicalComplex.homologyMap (Excision.bottomSES Y A).f q = 0 :=
    hA_zero.eq_of_src _ _
  exact hexact.isZero_X₂ hf_zero hg_zero
end CWComplex.SkeletonHomology
/-- Inductive step: if `H_q(X_k) = 0` and `k+1 < q`, then `H_q(X_{k+1}) = 0`. -/
namespace CWComplex.SkeletonHomology

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[subspaceTopInclusion_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma subspaceTopInclusion_factor
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k m : ℕ}
-- given
  (hkm : k ≤ m) :
-- imply
  (Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) : Set ↥(CWComplex.skeleton X (m + 1) : Set X))) = skeletonPreimageInclusion k m hkm ≫ (Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) : Set ↥(CWComplex.skeleton X (m + 1) : Set X))) := by
-- proof
  ext ⟨_, _⟩; rfl

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[subspaceChainInclusion_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma subspaceChainInclusion_factor
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k m : ℕ}
-- given
  (hkm : k ≤ m) :
-- imply
  Excision.subspaceChainInclusion ↥(CWComplex.skeleton X (m + 1) : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) = Excision.singularChainZ.map (skeletonPreimageInclusion k m hkm) ≫ Excision.subspaceChainInclusion ↥(CWComplex.skeleton X (m + 1) : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X)) := by
-- proof
  show Excision.singularChainZ.map (Excision.subspaceTopInclusion _) =
    Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
  rw [← Excision.singularChainZ.map_comp, ← subspaceTopInclusion_factor k m hkm]

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[skeletonPreimageInclusion_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeletonPreimageInclusion_comm
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k m : ℕ}
-- given
  (hkm : k ≤ m) :
-- imply
  Excision.singularChainZ.map (skeletonPreimageInclusion k m hkm) ≫ (skeletonPreimageChainIso (X := X) m).hom = (skeletonPreimageAkChainIso (X := X) k m hkm).hom ≫ Excision.subspaceChainInclusion ↥(CWComplex.skeleton X m : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) := by
-- proof
  show Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _ =
    Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
  rw [← Excision.singularChainZ.map_comp, ← Excision.singularChainZ.map_comp]
  congr 1
set_option maxHeartbeats 1600000 in

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/--
[triple_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma triple_exact
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {n k m : ℕ}
-- given
  (hkm : k ≤ m) :
-- imply
  ∃ (S : ShortComplex AddCommGrpCat), S.X₁ = Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X m : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) ∧ S.X₂ = Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X (m + 1) : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) ∧ S.X₃ = Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X (m + 1) : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X)) ∧ S.Exact := by
-- proof
  set Y : Type := ↥(CWComplex.skeleton X (m + 1) : Set X)
  set Ak : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)
  set Am : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X)
  set f := Excision.singularChainZ.map (skeletonPreimageInclusion (X := X) k m hkm)
  set g := Excision.subspaceChainInclusion Y Am
  have hfg : f ≫ g = Excision.subspaceChainInclusion Y Ak :=
    (subspaceChainInclusion_factor (X := X) k m hkm).symm
  haveI hf_mono : Mono f := by
    haveI : Mono (skeletonPreimageInclusion (X := X) k m hkm) := by
      rw [TopCat.mono_iff_injective]
      intro ⟨a, ha⟩ ⟨b, hb⟩ h
      have h' : (a : Y) = (b : Y) := by
        have := congr_arg Subtype.val h
        simp only [skeletonPreimageInclusion, TopCat.ofHom] at this
        exact this
      exact Subtype.ext h'
    exact Functor.map_mono _ _
  haveI hg_mono : Mono g := Excision.subspaceChainInclusion_mono Y Am
  haveI hfg_mono : Mono (f ≫ g) := hfg ▸ Excision.subspaceChainInclusion_mono Y Ak
  have hse := Excision.thirdIso_shortExact f g
  have hexact := hse.homology_exact₂ n
  have hcomm := skeletonPreimageInclusion_comm (X := X) k m hkm
  have hcoker_iso : cokernel f ≅
    Excision.relativeSingularChainComplex
      ↥(CWComplex.skeleton X m : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) :=
    cokernel.mapIso f
      (Excision.subspaceChainInclusion
        ↥(CWComplex.skeleton X m : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)))
      (skeletonPreimageAkChainIso (X := X) k m hkm)
      (skeletonPreimageChainIso (X := X) m)
      hcomm
  have hhom_iso : (cokernel f).homology n ≅
    Excision.RelativeSingularHomologyGroup n
      ↥(CWComplex.skeleton X m : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso hcoker_iso
  set ses := ShortComplex.mk
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))
    (by apply (cancel_epi (cokernel.π f)).mp
      simp only [comp_zero, cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc,
        Category.id_comp, cokernel.condition])
  set S := ShortComplex.mk
    (hhom_iso.inv ≫ HomologicalComplex.homologyMap ses.f n)
    (HomologicalComplex.homologyMap ses.g n)
    (by simp only [Category.assoc, ← HomologicalComplex.homologyMap_comp, ses.zero,
      HomologicalComplex.homologyMap_zero, comp_zero])
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  ·
    rfl
  ·
    show (cokernel (f ≫ g)).homology n = _
    rw [hfg]; rfl
  ·
    rfl
  ·
    have e : S ≅ ShortComplex.mk
      (HomologicalComplex.homologyMap ses.f n)
      (HomologicalComplex.homologyMap ses.g n)
      (by rw [← HomologicalComplex.homologyMap_comp, ses.zero,
        HomologicalComplex.homologyMap_zero]) :=
      ShortComplex.isoMk hhom_iso.symm (Iso.refl _) (Iso.refl _)
        (by simp [S]) (by simp [S])
    exact (ShortComplex.exact_iff_of_iso e).mpr hexact

end CWComplex.SkeletonHomology

/--
[CWComplex.SkeletonHomology.relativeHomology_triple_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma CWComplex.SkeletonHomology.relativeHomology_triple_step
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {n k m : ℕ}
-- given
  (hkm : k ≤ m)
  (h_step : IsZero (Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X (m + 1) : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X))))
  (h_prev : IsZero (Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X m : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X))))
  (_h_prev_lo : ∀ (j : ℕ), (ComplexShape.down ℕ).Rel n j → IsZero (Excision.RelativeSingularHomologyGroup j ↥(CWComplex.skeleton X m : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)))) :
-- imply
  IsZero (Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X (m + 1) : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X))) := by
-- proof
  obtain ⟨S, hS1, hS2, hS3, hexact⟩ :=
    CWComplex.SkeletonHomology.triple_exact (X := X) n k m hkm
  have hX1_zero : IsZero S.X₁ := hS1 ▸ h_prev
  have hX3_zero : IsZero S.X₃ := hS3 ▸ h_step
  have hf : S.f = 0 := hX1_zero.eq_of_src _ _
  have hg : S.g = 0 := hX3_zero.eq_of_tgt _ _
  have hX2_zero : IsZero S.X₂ := hexact.isZero_X₂ hf hg
  exact hS2 ▸ hX2_zero

/--
[CWComplex.SkeletonHomology.relativeHomology_self_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma CWComplex.SkeletonHomology.relativeHomology_self_isZero
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {n k : ℕ} :
-- imply
  IsZero (Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X k : Set X) (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X))) := by
-- proof
  have h_eq : (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
    Set ↥(CWComplex.skeleton X k : Set X)) = Set.univ := by
    ext ⟨_, hx⟩; simp [Set.mem_preimage, hx]
  rw [show Excision.RelativeSingularHomologyGroup n
    ↥(CWComplex.skeleton X k : Set X)
    (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) =
    Excision.RelativeSingularHomologyGroup n
      ↥(CWComplex.skeleton X k : Set X) Set.univ from by rw [h_eq]]
  unfold Excision.RelativeSingularHomologyGroup Excision.relativeSingularChainComplex
    Excision.subspaceChainInclusion
  haveI : IsIso (Excision.subspaceTopInclusion (Set.univ :
    Set ↥(CWComplex.skeleton X k : Set X))) := by
    have : Excision.subspaceTopInclusion (Set.univ :
      Set ↥(CWComplex.skeleton X k : Set X)) =
      (TopCat.isoOfHomeo (Homeomorph.Set.univ
        ↥(CWComplex.skeleton X k : Set X))).hom := by
      ext x; simp [Excision.subspaceTopInclusion, TopCat.isoOfHomeo, Homeomorph.Set.univ]
    rw [this]; infer_instance
  haveI : IsIso (Excision.singularChainZ.map (Excision.subspaceTopInclusion (Set.univ :
    Set ↥(CWComplex.skeleton X k : Set X)))) :=
    Excision.singularChainZ.map_isIso _
  exact Functor.map_isZero _ (isZero_cokernel_of_epi _)

namespace CWHomology

/--
[skeletonInclusionMap_comp_skeletonConnectingHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeletonInclusionMap_comp_skeletonConnectingHom
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {n : ℕ} :
-- imply
  skeletonInclusionMap X (n + 1) ≫ skeletonConnectingHom X n = 0 := by
-- proof
  let Y : Type := ↥(CWComplex.skeleton X (n + 1) : Set X)
  let A : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X n : Set X)
  have hse := Excision.bottomSES_shortExact Y A
  have hRel : (ComplexShape.down ℕ).Rel (n + 1) n := rfl
  let delta := hse.δ (n + 1) n hRel
  let hA_homeo : ↥A ≃ₜ ↥(CWComplex.skeleton X n : Set X) :=
    { toEquiv := {
      toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
        (by norm_cast; omega) hx⟩, hx⟩
      left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
      right_inv := fun ⟨x, _⟩ => rfl }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let hA_iso : TopCat.of ↥A ≅ TopCat.of ↥(CWComplex.skeleton X n : Set X) :=
    TopCat.isoOfHomeo hA_homeo
  let hhom_iso :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (Excision.singularChainZ.mapIso hA_iso)
  have hincl : skeletonInclusionMap X (n + 1) =
    HomologicalComplex.homologyMap (Excision.bottomSES Y A).g (n + 1) := rfl
  have hconn : skeletonConnectingHom X n = delta ≫ hhom_iso.hom := rfl
  rw [hincl, hconn]
  have h_comp_delta := hse.comp_δ (n + 1) n hRel
  change HomologicalComplex.homologyMap (Excision.bottomSES Y A).g (n + 1) ≫
    hse.δ (n + 1) n hRel ≫ hhom_iso.hom = 0
  rwa [reassoc_of% h_comp_delta]

end CWHomology

namespace CWHomology

/--
[skeletonConnectingHom_comp_skeletonStepMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeletonConnectingHom_comp_skeletonStepMap
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {n : ℕ} :
-- imply
  skeletonConnectingHom X n ≫ skeletonStepMap X n = 0 := by
-- proof
  let Y : Type := ↥(CWComplex.skeleton X (n + 1) : Set X)
  let A : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X n : Set X)
  have hse := Excision.bottomSES_shortExact Y A
  have hRel : (ComplexShape.down ℕ).Rel (n + 1) n := rfl
  let delta := hse.δ (n + 1) n hRel
  let hA_homeo : ↥A ≃ₜ ↥(CWComplex.skeleton X n : Set X) :=
    { toEquiv := {
      toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
        (by norm_cast; omega) hx⟩, hx⟩
      left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
      right_inv := fun ⟨x, _⟩ => rfl }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let hA_iso : TopCat.of ↥A ≅ TopCat.of ↥(CWComplex.skeleton X n : Set X) :=
    TopCat.isoOfHomeo hA_homeo
  let hhom_iso :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (Excision.singularChainZ.mapIso hA_iso)
  have hconn : skeletonConnectingHom X n = delta ≫ hhom_iso.hom := rfl
  have htop_eq : Excision.subspaceTopInclusion A =
    hA_iso.hom ≫ CWComplex.SkeletonHomology.skeletonStepInclusion X n := by
    ext ⟨⟨x, hx_k1⟩, hx_k⟩
    simp only [CategoryTheory.comp_apply]
    rfl
  have hchain_eq : (Excision.bottomSES Y A).f =
    Excision.singularChainZ.map hA_iso.hom ≫
    Excision.singularChainZ.map (CWComplex.SkeletonHomology.skeletonStepInclusion X n) := by
    show Excision.subspaceChainInclusion Y A = _
    show Excision.singularChainZ.map (Excision.subspaceTopInclusion A) = _
    rw [htop_eq, Excision.singularChainZ.map_comp]
  have hhom_eq : HomologicalComplex.homologyMap (Excision.bottomSES Y A).f n =
    hhom_iso.hom ≫ CWComplex.SkeletonHomology.skeletonStepHomologyMap X n n := by
    show (HomologicalComplex.homologyFunctor _ _ n).map ((Excision.bottomSES Y A).f) =
      (HomologicalComplex.homologyFunctor _ _ n).map (Excision.singularChainZ.map hA_iso.hom) ≫
      (HomologicalComplex.homologyFunctor _ _ n).map
        (Excision.singularChainZ.map (CWComplex.SkeletonHomology.skeletonStepInclusion X n))
    rw [hchain_eq]
    exact (HomologicalComplex.homologyFunctor _ _ n).map_comp _ _
  have hstep : skeletonStepMap X n = CWComplex.SkeletonHomology.skeletonStepHomologyMap X n n := rfl
  rw [hconn, hstep]
  have h_delta_comp := hse.δ_comp (n + 1) n hRel
  rw [hhom_eq] at h_delta_comp
  change (hse.δ (n + 1) n hRel ≫ hhom_iso.hom) ≫
    CWComplex.SkeletonHomology.skeletonStepHomologyMap X n n = 0
  rwa [Category.assoc]

end CWHomology

namespace CWHomology

/--
[skeletonInclusion_cellularMap_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeletonInclusion_cellularMap_comm
  {n : ℕ}
  {X : Type}
  {Y : Type}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [T2Space X]
  [T2Space Y]
  [Topology.CWComplex (Set.univ : Set X)]
  [Topology.CWComplex (Set.univ : Set Y)]
  {f : C(X, Y)}
-- given
  (hf : IsCellularMap f) :
-- imply
  CWComplex.SkeletonHomology.skeletonInclusion X (n + 1) ≫ TopCat.ofHom f = cellularMapOnSkeleton f hf (n + 1) ≫ CWComplex.SkeletonHomology.skeletonInclusion Y (n + 1) := by
-- proof
  ext ⟨x, hx⟩; rfl

end CWHomology

namespace CWHomology

/--
[skeletonHomologyMap_naturality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma skeletonHomologyMap_naturality
  {n : ℕ}
  {X : Type}
  {Y : Type}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [T2Space X]
  [T2Space Y]
  [Topology.CWComplex (Set.univ : Set X)]
  [Topology.CWComplex (Set.univ : Set Y)]
  {f : C(X, Y)}
-- given
  (hf : IsCellularMap f) :
-- imply
  skeletonHomologyMapInduced n f hf ≫ CWComplex.SkeletonHomology.skeletonHomologyMap Y n (n + 1) = CWComplex.SkeletonHomology.skeletonHomologyMap X n (n + 1) ≫ singularHomologyMap n f := by
-- proof
  show ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
    (cellularMapOnSkeleton f hf (n + 1)) ≫
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
      (CWComplex.SkeletonHomology.skeletonInclusion Y (n + 1)) =
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
      (CWComplex.SkeletonHomology.skeletonInclusion X (n + 1)) ≫
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)
  rw [← Functor.map_comp, ← Functor.map_comp,
    skeletonInclusion_cellularMap_comm]
/-- Naturality of the intermediate isomorphism `H_n(C_*(X)) ≅ H_n(X_{n+1})` with respect
to cellular maps — this gives the filtration-preserving-naturality statement of
Theorem 16.3. -/
end CWHomology
namespace CellularHomology
open Topology


namespace CellularHomology

/--
[cellularChains_odd_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
lemma cellularChains_odd_subsingleton
  {X : Type}
  [TopologicalSpace X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k : ℕ}
-- given
  (heven : HasOnlyEvenCells X) :
-- imply
  Subsingleton (CWComplex.cellularChains X (2 * k + 1)) := by
-- proof
  haveI := heven k
  infer_instance
/-- **Corollary 16.4.** For a CW complex `X` with only even cells, all cellular
boundary maps vanish, so the singular homology in degree `n` is isomorphic to the
cellular chain group `C_n(X) = ℤ^{(\text{cells in deg } n)}`. In particular,
`H_n(X) = 0` for `n` odd, is free abelian for all `n`, and has rank equal to the
number of `n`-cells in even degrees. -/

end CellularHomology

/--
[CWComplex.SkeletonHomology.skelPairSquare_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
private lemma skelPairSquare_comm_eq
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k m : ℕ} :
-- imply
  Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) : Set ↥(CWComplex.skeleton X m : Set X)) ≫ CWComplex.SkeletonHomology.skeletonInclusion X m = CWComplex.SkeletonHomology.skelPairSubspaceMap k m ≫ Excision.subspaceTopInclusion (↑(CWComplex.skeleton X k : Set X) : Set X) := by
-- proof
  apply CWComplex.SkeletonHomology.skelPairSquare_comm k m

/--
[cellularMapSquare_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean)
-/
@[path]
private lemma cellularMapSquare_comm_eq
  {X : Type}
  {Y : Type}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [T2Space X]
  [T2Space Y]
  [Topology.CWComplex (Set.univ : Set X)]
  [Topology.CWComplex (Set.univ : Set Y)]
  {f : C(X, Y)}
  {n : ℕ}
-- given
  (hf : IsCellularMap f) :
-- imply
  Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X) : Set ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)) ≫ cellularMapOnSkeleton f hf n = cellularMapOnPrevSkeleton f hf n ≫ Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y) : Set ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)) := by
-- proof
  apply CWHomology.cellularMapSquare_comm f hf n


-- created on 2026-10-23
