import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall.Part3
open Classical in AlgebraicTopologyI


namespace AlgebraicTopologyI

/--
[isSmallChain_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
lemma isSmallChain_zero
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ} :
-- imply
  IsSmallChain 𝒜 (0 : SingularChains n X) := by
-- proof
  intro σ hσ
  exfalso
  have : σ ∈ (∅ : Finset (SingularSimplex n X)) := by
    rwa [← FreeAbelianGroup.support_zero]
  simp at this

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[isSmallChain_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
lemma isSmallChain_add
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {a b : SingularChains n X}
-- given
  (ha : IsSmallChain 𝒜 a)
  (hb : IsSmallChain 𝒜 b) :
-- imply
  IsSmallChain 𝒜 (a + b) := by
-- proof
  intro σ hσ
  obtain h | h := Finset.mem_union.mp (FreeAbelianGroup.support_add a b hσ)
  · exact ha σ h
  · exact hb σ h

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[SingularChains.map_comp'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
lemma SingularChains.map_comp'
  [TopologicalSpace X]
  {n : ℕ}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [TopologicalSpace Z]
  {f : C(Y, Z)}
  {g : C(X, Y)}
  {s : SingularChains n X} :
-- imply
  SingularChains.map (f.comp g) s = SingularChains.map f (SingularChains.map g s) := by
-- proof
  show (FreeAbelianGroup.map (SingularSimplex.map (f.comp g))) s =
    (FreeAbelianGroup.map (SingularSimplex.map f))
      ((FreeAbelianGroup.map (SingularSimplex.map g)) s)
  rw [← FreeAbelianGroup.map_comp_apply]
  congr 1

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[subdivisionOp_map_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
lemma subdivisionOp_map_comm
  [TopologicalSpace X]
  {n : ℕ}
  [TopologicalSpace Y]
  [TopologicalSpace X]
  {f : C(Y, X)}
  {c : SingularChains n Y} :
-- imply
  subdivisionOp n X (SingularChains.map f c) = SingularChains.map f (subdivisionOp n Y c) := by
-- proof
  have h_eq : (subdivisionOp n X).comp (SingularChains.map f) =
    (SingularChains.map f).comp (subdivisionOp n Y) := by
    apply FreeAbelianGroup.lift_ext
    intro η
    show subdivisionOp n X (SingularChains.map f (FreeAbelianGroup.of η)) =
      SingularChains.map f (subdivisionOp n Y (FreeAbelianGroup.of η))
    calc subdivisionOp n X (SingularChains.map f (FreeAbelianGroup.of η))
      = subdivisionOp n X (FreeAbelianGroup.of (SingularSimplex.map f η)) := by
        congr 1
      _ = SingularChains.map (SingularSimplex.map f η) (stdSubdivisionChain n) :=
        FreeAbelianGroup.lift_apply_of _ _
      _ = SingularChains.map f (SingularChains.map η (stdSubdivisionChain n)) := by
        rw [SingularSimplex.map]; exact SingularChains.map_comp' f η _
      _ = SingularChains.map f (subdivisionOp n Y (FreeAbelianGroup.of η)) := by
        congr 1; exact (FreeAbelianGroup.lift_apply_of _ _).symm
  exact DFunLike.congr_fun h_eq c

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[subdivisionOp_naturality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
lemma subdivisionOp_naturality
  [TopologicalSpace X]
  {n : ℕ}
  [TopologicalSpace X]
  {σ : SingularSimplex n X}
  {k : ℕ} :
-- imply
  iterateSubdivision k (FreeAbelianGroup.of σ) = SingularChains.map (show C(↥(stdSimplex ℝ (Fin (n + 1))), X) from σ) (iterateSubdivision k (FreeAbelianGroup.of (ContinuousMap.id ↥(stdSimplex ℝ (Fin (n + 1)))))) := by
-- proof
  induction k with
  | zero =>
    show FreeAbelianGroup.of σ =
      SingularChains.map σ (FreeAbelianGroup.of (ContinuousMap.id _))
    conv_rhs => rw [show SingularChains.map σ (FreeAbelianGroup.of (ContinuousMap.id _)) =
      FreeAbelianGroup.of (SingularSimplex.map σ (ContinuousMap.id _)) from by
      show (FreeAbelianGroup.map _) _ = _; simp]
    simp [SingularSimplex.map, ContinuousMap.comp_id]
  | succ k ih =>
    have step_lhs : iterateSubdivision (k + 1) (FreeAbelianGroup.of σ) =
      subdivisionOp n X (iterateSubdivision k (FreeAbelianGroup.of σ)) := by
      show (((⇑(subdivisionOp n X))^[k + 1]) (FreeAbelianGroup.of σ)) =
        (subdivisionOp n X) (((⇑(subdivisionOp n X))^[k]) (FreeAbelianGroup.of σ))
      rw [Function.iterate_succ']; rfl
    have step_rhs : iterateSubdivision (k + 1)
      (FreeAbelianGroup.of (ContinuousMap.id ↥(stdSimplex ℝ (Fin (n + 1))))) =
      subdivisionOp n _ (iterateSubdivision k
        (FreeAbelianGroup.of (ContinuousMap.id ↥(stdSimplex ℝ (Fin (n + 1)))))) := by
      show (((⇑(subdivisionOp n _))^[k + 1]) _) = (subdivisionOp n _) (((⇑(subdivisionOp n _))^[k]) _)
      rw [Function.iterate_succ']; rfl
    rw [step_lhs, ih, subdivisionOp_map_comm, step_rhs]
/-- Single-simplex form of Lemma 13.2: for a cover `𝒜` of `X` and any singular simplex
`σ`, some iterate of the subdivision operator sends `σ` to an `𝒜`-small chain. -/
end AlgebraicTopologyI


/--
[toFreeAbelianGroup_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma toFreeAbelianGroup_eq_sum_eq
  {f : Y →₀ ℤ} :
-- imply
  Finsupp.toFreeAbelianGroup f = f.sum (fun x n => n • FreeAbelianGroup.of x) := by
-- proof
  apply toFreeAbelianGroup_eq_sum f

/--
[freeAbelianGroup_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma freeAbelianGroup_eq_sum_eq
  {c : FreeAbelianGroup Y} :
-- imply
  c = (FreeAbelianGroup.toFinsupp c).sum (fun x n => n • FreeAbelianGroup.of x) := by
-- proof
  apply freeAbelianGroup_eq_sum c

/--
[lift_eq_finsupp_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma lift_eq_finsupp_sum_eq
  [AddCommGroup Z]
  {f : Y → Z}
  {c : FreeAbelianGroup Y} :
-- imply
  (FreeAbelianGroup.lift f) c = (FreeAbelianGroup.toFinsupp c).sum (fun x n => n • f x) := by
-- proof
  apply lift_eq_finsupp_sum f c

/--
[support_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma support_finset_sum_eq
  {s : Finset Y}
  {f : Y → FreeAbelianGroup Z} :
-- imply
  (∑ i ∈ s, f i).support ⊆ s.biUnion (fun i => (f i).support) := by
-- proof
  apply support_finset_sum s f

/--
[support_lift_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma support_lift_subset_eq
  {f : Y → FreeAbelianGroup Z}
  {c : FreeAbelianGroup Y} :
-- imply
  ((FreeAbelianGroup.lift f) c).support ⊆ c.support.biUnion (fun x => (f x).support) := by
-- proof
  apply support_lift_subset f c

/--
[lift_support_forall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma lift_support_forall_eq
  {f : Y → FreeAbelianGroup Z}
  {c : FreeAbelianGroup Y}
-- given
  (P : Z → Prop)
  (hP : ∀ x ∈ c.support, ∀ y ∈ (f x).support, P y) :
-- imply
  ∀ y ∈ ((FreeAbelianGroup.lift f) c).support, P y := by
-- proof
  apply lift_support_forall f c P hP

/--
[barySubdivVertex_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma barySubdivVertex_nonneg_eq
  [TopologicalSpace X]
  {n : ℕ}
  {π : Equiv.Perm (Fin (n + 1))}
  {k i : Fin (n + 1)} :
-- imply
  0 ≤ barySubdivVertex n π k i := by
-- proof
  apply AlgebraicTopologyI.barySubdivVertex_nonneg n π k i

/--
[barySubdivVertex_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma barySubdivVertex_sum_eq
  [TopologicalSpace X]
  {n : ℕ}
  {π : Equiv.Perm (Fin (n + 1))}
  {k : Fin (n + 1)} :
-- imply
  ∑ i : Fin (n + 1), barySubdivVertex n π k i = 1 := by
-- proof
  apply AlgebraicTopologyI.barySubdivVertex_sum n π k

/--
[barySubdivMapFn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma barySubdivMapFn_mem_eq
  [TopologicalSpace X]
  {n : ℕ}
  {π : Equiv.Perm (Fin (n + 1))}
  {t : Fin (n + 1) → ℝ}
-- given
  (ht : t ∈ stdSimplex ℝ (Fin (n + 1))) :
-- imply
  barySubdivMapFn n π t ∈ stdSimplex ℝ (Fin (n + 1)) := by
-- proof
  apply AlgebraicTopologyI.barySubdivMapFn_mem n π t ht

/--
[barySubdivMap_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma barySubdivMap_continuous_eq
  [TopologicalSpace X]
  {n : ℕ}
  {π : Equiv.Perm (Fin (n + 1))} :
-- imply
  Continuous (fun (t : ↥(stdSimplex ℝ (Fin (n + 1)))) => (⟨barySubdivMapFn n π t.1, barySubdivMapFn_mem n π t.1 t.2⟩ : ↥(stdSimplex ℝ (Fin (n + 1))))) := by
-- proof
  apply AlgebraicTopologyI.barySubdivMap_continuous n π

/--
[iterateSubdivision_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma iterateSubdivision_add_eq
  [TopologicalSpace X]
  {n : ℕ}
  {k : ℕ}
  {a b : SingularChains n X} :
-- imply
  iterateSubdivision k (a + b) = iterateSubdivision k a + iterateSubdivision k b := by
-- proof
  apply AlgebraicTopologyI.iterateSubdivision_add k a b

/--
[range_subset_of_mem_support_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma range_subset_of_mem_support_map_eq
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [TopologicalSpace Z]
  {n : ℕ}
  {σ : C(Y, Z)}
  {c : SingularChains n Y}
  {τ : SingularSimplex n Z}
-- given
  (hτ : τ ∈ FreeAbelianGroup.support (SingularChains.map σ c)) :
-- imply
  Set.range (show C(↥(stdSimplex ℝ (Fin (n + 1))), Z) from τ) ⊆ Set.range σ := by
-- proof
  apply AlgebraicTopologyI.range_subset_of_mem_support_map σ c τ hτ

/--
[isSmallChain_subdivisionOp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma isSmallChain_subdivisionOp_eq
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {c : SingularChains n X}
-- given
  (h : IsSmallChain 𝒜 c) :
-- imply
  IsSmallChain 𝒜 (subdivisionOp n X c) := by
-- proof
  apply AlgebraicTopologyI.isSmallChain_subdivisionOp h

/--
[isSmallChain_iterateSubdivision_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma isSmallChain_iterateSubdivision_succ_eq
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {c : SingularChains n X}
  {k : ℕ}
-- given
  (h : IsSmallChain 𝒜 (iterateSubdivision k c)) :
-- imply
  IsSmallChain 𝒜 (iterateSubdivision (k + 1) c) := by
-- proof
  apply AlgebraicTopologyI.isSmallChain_iterateSubdivision_succ h

/--
[isSmallChain_iterateSubdivision_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean)
-/
@[path]
private lemma isSmallChain_iterateSubdivision_mono_eq
  [TopologicalSpace X]
  {𝒜 : Set (Set X)}
  {n : ℕ}
  {c : SingularChains n X}
  {k : ℕ}
  {j : ℕ}
-- given
  (h : IsSmallChain 𝒜 (iterateSubdivision k c)) :
-- imply
  IsSmallChain 𝒜 (iterateSubdivision (k + j) c) := by
-- proof
  apply AlgebraicTopologyI.isSmallChain_iterateSubdivision_mono h j


-- created on 2026-10-23
