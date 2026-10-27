import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
open CategoryTheory AlgebraicTopologyI Finset BigOperators BarycentricSubdivision LocalityPrinciple


namespace LocalityPrinciple

/--
[faceInclusion_comp_faceInclusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
lemma faceInclusion_comp_faceInclusion
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {i : Fin (n + 2)}
  {j : Fin (n + 3)}
-- given
  (hij : (j : ℕ) ≤ (i : ℕ))
  (hj : j.val < n + 2) :
-- imply
  (faceInclusion (n + 1) i.succ).comp (faceInclusion n (Fin.castLT j hj)) = (faceInclusion (n + 1) j).comp (faceInclusion n i) := by
-- proof
  ext ⟨t, ht⟩ : 1
  simp only [ContinuousMap.comp_apply, faceInclusion]
  apply Subtype.ext
  show Fin.insertNth (α := fun _ => ℝ) i.succ 0 (Fin.insertNth (α := fun _ => ℝ) (Fin.castLT j hj) 0 t) =
    Fin.insertNth (α := fun _ => ℝ) j 0 (Fin.insertNth (α := fun _ => ℝ) i 0 t)
  funext ⟨m, hm⟩
  simp only [Fin.insertNth, Fin.succAboveCases, Fin.succAbove, eq_rec_constant]
  have hi_bound := i.isLt
  have hj_bound := j.isLt
  simp only [Fin.ext_iff, Fin.lt_def, Fin.castLT, Fin.succ,
    Fin.coe_castPred, Fin.val_pred]
  split_ifs <;> first | omega | rfl

end LocalityPrinciple

namespace LocalityPrinciple

/--
[faceInclusion_eq_stdSimplex_map_succAbove](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
lemma faceInclusion_eq_stdSimplex_map_succAbove
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {i : Fin (n + 2)} :
-- imply
  faceInclusion n i = ⟨stdSimplex.map (Fin.succAbove i), stdSimplex.continuous_map _⟩ := by
-- proof
  ext t j
  simp only [faceInclusion, ContinuousMap.coe_mk]
  change Fin.insertNth (α := fun _ => ℝ) i 0 t.1 j =
    (stdSimplex.map (Fin.succAbove i) t).1 j
  change _ = (FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i)) t.1 j
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hj : j = i
  · subst hj
    rw [Fin.insertNth_apply_same]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact absurd hx.2 (Fin.succAbove_ne _ x)
  · have hj' : ∃ k, i.succAbove k = j :=
    Fin.exists_succAbove_eq hj
    obtain ⟨k, hk⟩ := hj'
    rw [show Fin.insertNth (α := fun _ => ℝ) i 0 t.1 j = t.1 k from by
      conv_lhs => rw [← hk]; rw [Fin.insertNth_apply_succAbove]]
    symm
    have h_filter : Finset.univ.filter (fun x => i.succAbove x = j) = {k} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hx => Fin.succAbove_right_injective (hx.trans hk.symm),
        fun hx => by rw [hx, hk]⟩
    rw [h_filter, Finset.sum_singleton]
set_option maxHeartbeats 800000 in

end LocalityPrinciple

namespace LocalityPrinciple

/--
[hom_finsum_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
lemma hom_finsum_apply_one
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {B : AddCommGrpCat}
  {n : ℕ}
  {f : Fin n → (AddCommGrpCat.of ℤ ⟶ B)} :
-- imply
  (ConcreteCategory.hom (∑ i : Fin n, f i)) (1 : ℤ) = ∑ i : Fin n, (ConcreteCategory.hom (f i)) (1 : ℤ) := by
-- proof
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact map_zero (ConcreteCategory.hom (0 : AddCommGrpCat.of ℤ ⟶ B))
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, AddCommGrpCat.hom_add_apply]
    congr 1
    exact ih (fun i => f i.succ)
open Limits AlgebraicTopology SimplexCategory in
set_option maxHeartbeats 1600000 in

end LocalityPrinciple

namespace LocalityPrinciple

/--
[singularChainsLift_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
lemma singularChainsLift_surjective
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {X : TopCat.{0}}
  {n : ℕ} :
-- imply
  Function.Surjective (singularChainsLift X n) := by
-- proof
  set β := (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))
  set e := (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm
  let section_hom : (∐ (fun _ : β => AddCommGrpCat.of ℤ) : AddCommGrpCat) ⟶
    AddCommGrpCat.of (FreeAbelianGroup (SingularSimplex n X)) :=
    Limits.Sigma.desc (fun b => AddCommGrpCat.ofHom {
      toFun := fun m => m • FreeAbelianGroup.of (e.symm b)
      map_zero' := zero_zsmul _
      map_add' := fun x y => add_zsmul (FreeAbelianGroup.of (e.symm b)) x y
    })
  let forward_hom : AddCommGrpCat.of (FreeAbelianGroup (SingularSimplex n X)) ⟶
    (∐ (fun _ : β => AddCommGrpCat.of ℤ) : AddCommGrpCat) :=
    AddCommGrpCat.ofHom (singularChainsLift X n)
  have h_comp : section_hom ≫ forward_hom = 𝟙 _ := by
    apply Limits.Sigma.hom_ext
    intro b
    simp only [section_hom, Limits.Sigma.ι_desc_assoc, Category.comp_id]
    apply AddCommGrpCat.ext
    intro m
    change (FreeAbelianGroup.lift (fun σ =>
      (Limits.Sigma.ι (fun _ : β => AddCommGrpCat.of ℤ) (e σ)) (1 : ℤ)))
      ((m : ℤ) • FreeAbelianGroup.of (e.symm b)) =
      (Limits.Sigma.ι (fun _ : β => AddCommGrpCat.of ℤ) b) (m : ℤ)
    rw [map_zsmul, FreeAbelianGroup.lift_apply_of, Equiv.apply_symm_apply,
      ← map_zsmul (ConcreteCategory.hom
        (Limits.Sigma.ι (fun _ : β => AddCommGrpCat.of ℤ) b)) m (1 : ℤ),
      zsmul_one]
    rfl
  intro y
  exact ⟨(ConcreteCategory.hom section_hom) y, ConcreteCategory.congr_hom h_comp y⟩

end LocalityPrinciple

namespace LocalityPrinciple

/--
[endoPow_succ_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
lemma endoPow_succ_right
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {C : ChainComplex AddCommGrpCat ℕ}
  {f : C ⟶ C}
  {k : ℕ} :
-- imply
  endoPow f (k + 1) = endoPow f k ≫ f := by
-- proof
  induction k with
  | zero =>
    simp only [endoPow_zero, endoPow_succ, Category.id_comp, Category.comp_id]
  | succ k ih =>
    conv_lhs => rw [endoPow_succ, ih, ← Category.assoc, ← endoPow_succ]

end LocalityPrinciple

namespace LocalityPrinciple

/--
[singularChainsLift_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
lemma singularChainsLift_injective
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {X : TopCat.{0}}
  {n : ℕ} :
-- imply
  Function.Injective (singularChainsLift X n) := by
-- proof
  set β := (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))
  set e := (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm
  let retract_hom : (∐ (fun _ : β => AddCommGrpCat.of ℤ) : AddCommGrpCat) ⟶
    AddCommGrpCat.of (FreeAbelianGroup (SingularSimplex n X)) :=
    Limits.Sigma.desc (fun b => AddCommGrpCat.ofHom {
      toFun := fun m => m • FreeAbelianGroup.of (e.symm b)
      map_zero' := zero_zsmul _
      map_add' := fun x y => add_zsmul (FreeAbelianGroup.of (e.symm b)) x y
    })
  let forward_hom : AddCommGrpCat.of (FreeAbelianGroup (SingularSimplex n X)) ⟶
    (∐ (fun _ : β => AddCommGrpCat.of ℤ) : AddCommGrpCat) :=
    AddCommGrpCat.ofHom (singularChainsLift X n)
  have h_left_inv : forward_hom ≫ retract_hom = 𝟙 _ := by
    apply AddCommGrpCat.ext
    intro x
    change (AddCommGrpCat.Hom.hom retract_hom)
      ((AddCommGrpCat.Hom.hom forward_hom) x) = x
    induction x using FreeAbelianGroup.induction_on' with
    | zero => simp [map_zero]
    | pure σ =>
      show (AddCommGrpCat.Hom.hom retract_hom)
        ((singularChainsLift X n) (FreeAbelianGroup.of σ)) =
        FreeAbelianGroup.of σ
      change (ConcreteCategory.hom retract_hom)
        ((FreeAbelianGroup.lift (fun σ =>
          (Limits.Sigma.ι (fun _ : β => AddCommGrpCat.of ℤ) (e σ)) (1 : ℤ)))
          (FreeAbelianGroup.of σ)) =
        FreeAbelianGroup.of σ
      rw [FreeAbelianGroup.lift_apply_of]
      show (ConcreteCategory.hom (Limits.Sigma.desc (fun b => AddCommGrpCat.ofHom {
        toFun := fun m => m • FreeAbelianGroup.of (e.symm b)
        map_zero' := zero_zsmul _
        map_add' := fun x y => add_zsmul (FreeAbelianGroup.of (e.symm b)) x y
        })))
        ((ConcreteCategory.hom (Limits.Sigma.ι (fun _ : β => AddCommGrpCat.of ℤ) (e σ))) 1) =
        FreeAbelianGroup.of σ
      have h_desc := ConcreteCategory.congr_hom
        (Limits.Sigma.ι_desc (fun b => AddCommGrpCat.ofHom {
          toFun := fun m => m • FreeAbelianGroup.of (e.symm b)
          map_zero' := zero_zsmul _
          map_add' := fun x y => add_zsmul (FreeAbelianGroup.of (e.symm b)) x y
        }) (e σ)) (1 : ℤ)
      simp only [ConcreteCategory.comp_apply] at h_desc
      rw [h_desc]
      show (1 : ℤ) • FreeAbelianGroup.of (e.symm (e σ)) = FreeAbelianGroup.of σ
      rw [one_zsmul, Equiv.symm_apply_apply]
      rfl
    | neg σ ih =>
      show (AddCommGrpCat.Hom.hom retract_hom)
        ((AddCommGrpCat.Hom.hom forward_hom) (-FreeAbelianGroup.of σ)) =
        -(FreeAbelianGroup.of σ)
      rw [map_neg, map_neg]
      exact congrArg (- ·) ih
    | add x y ihx ihy =>
      rw [map_add, map_add, ihx, ihy]
  exact Function.HasLeftInverse.injective
    ⟨AddCommGrpCat.Hom.hom retract_hom,
      fun x => ConcreteCategory.congr_hom h_left_inv x⟩

end LocalityPrinciple

namespace LocalityPrinciple

/--
[boundaryMap_map_comm_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
lemma boundaryMap_map_comm_local
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {n : ℕ}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {f : C(X, Y)}
  {s : SingularChains (n + 1) X} :
-- imply
  boundaryMap n Y (SingularChains.map f s) = SingularChains.map f (boundaryMap n X s) := by
-- proof
  have h_eq : (boundaryMap n Y).comp (SingularChains.map f) =
    (SingularChains.map f).comp (boundaryMap n X) := by
    apply FreeAbelianGroup.lift_ext
    intro sigma
    show (boundaryMap n Y) (FreeAbelianGroup.of (SingularSimplex.map f sigma)) =
      (SingularChains.map f) ((boundaryMap n X) (FreeAbelianGroup.of sigma))
    unfold boundaryMap SingularChains.map SingularSimplex.map SingularSimplex.face
    erw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, map_sum]
    congr 1; ext i : 1
    erw [map_zsmul, FreeAbelianGroup.map_of_apply]
    rfl
  exact DFunLike.congr_fun h_eq s

end LocalityPrinciple

/--
[isSmall_face](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
private lemma isSmall_face_eq
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {n : ℕ}
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {σ : SingularSimplex (n + 1) X}
  {i : Fin (n + 2)}
-- given
  (hσ : IsSmall 𝒜 σ) :
-- imply
  IsSmall 𝒜 (SingularSimplex.face i σ) := by
-- proof
  apply LocalityPrinciple.isSmall_face X 𝒜 𝒜 σ hσ i

/--
[boundaryMap_mem_smallChainSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
private lemma boundaryMap_mem_smallChainSubgroup_eq
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  {n : ℕ}
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {c : SingularChains (n + 1) X}
-- given
  (hc : c ∈ smallChainSubgroup (n + 1) 𝒜) :
-- imply
  boundaryMap n X c ∈ smallChainSubgroup n 𝒜 := by
-- proof
  apply LocalityPrinciple.boundaryMap_mem_smallChainSubgroup X 𝒜 𝒜 c hc

/--
[isSmallChain_mem_smallChainSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
private lemma isSmallChain_mem_smallChainSubgroup_eq
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {c : SingularChains n X}
-- given
  (hc : IsSmallChain 𝒜 c) :
-- imply
  c ∈ smallChainSubgroup n 𝒜 := by
-- proof
  apply LocalityPrinciple.isSmallChain_mem_smallChainSubgroup X 𝒜 𝒜 c hc

/--
[isSmallChain_iterateSubdivision](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
private lemma isSmallChain_iterateSubdivision_eq
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {c : SingularChains n X}
  {k : ℕ}
-- given
  (h : IsSmallChain 𝒜 c) :
-- imply
  IsSmallChain 𝒜 (iterateSubdivision k c) := by
-- proof
  apply LocalityPrinciple.isSmallChain_iterateSubdivision X 𝒜 h k

/--
[iterateSubdivision_mem_smallChainSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
private lemma iterateSubdivision_mem_smallChainSubgroup_eq
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {k : ℕ}
  {c : SingularChains n X}
-- given
  (hc : c ∈ smallChainSubgroup n 𝒜) :
-- imply
  iterateSubdivision k c ∈ smallChainSubgroup n 𝒜 := by
-- proof
  apply LocalityPrinciple.iterateSubdivision_mem_smallChainSubgroup X 𝒜 𝒜 n k c hc

/--
[isSmallChain_homotopyOpK_of](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
private lemma isSmallChain_homotopyOpK_of_eq
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {k : ℕ}
  {σ : SingularSimplex n X}
-- given
  (hσ : IsSmall 𝒜 σ) :
-- imply
  IsSmallChain 𝒜 (homotopyOpK n k (FreeAbelianGroup.of σ)) := by
-- proof
  apply LocalityPrinciple.isSmallChain_homotopyOpK_of X 𝒜 𝒜 n k σ hσ

/--
[homotopyOpK_mem_smallChainSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean)
-/
@[path]
private lemma homotopyOpK_mem_smallChainSubgroup_eq
  {X : TopCat.{0}}
  {𝒜 : Set (Set X)}
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {k : ℕ}
  {c : SingularChains n X}
-- given
  (hc : c ∈ smallChainSubgroup n 𝒜) :
-- imply
  homotopyOpK n k c ∈ smallChainSubgroup (n + 1) 𝒜 := by
-- proof
  apply LocalityPrinciple.homotopyOpK_mem_smallChainSubgroup X 𝒜 𝒜 n k c hc


-- created on 2026-10-23
