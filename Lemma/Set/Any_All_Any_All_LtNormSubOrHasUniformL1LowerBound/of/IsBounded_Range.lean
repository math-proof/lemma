import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.NormedSpace.RosenthalL1.Part20

open FunctionalAnalysis.RosenthalL1Wanted


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_not_mem_of_rejects](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_not_mem_of_rejects
  {𝒜 : List ℕ → Prop} {s : List ℕ} {φ : ℕ → ℕ}
  (h : rosenthalRejects 𝒜 s φ) : ¬𝒜 s := by
  intro hs
  have ha : rosenthalAccepts 𝒜 s φ := by
    intro ψ hψ
    exact ⟨0, by simpa [rosenthalInitialSegment] using hs⟩
  exact h id strictMono_id (by simpa using ha)

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_fusionStates_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_fusionStates_succ
  (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) :
  rosenthalFusionStates 𝒜 st (n + 1) =
    rosenthalFusionNext 𝒜 (rosenthalFusionStates 𝒜 st n) := by
  rw [show n + 1 = n.succ from rfl]
  exact Function.iterate_succ_apply' (rosenthalFusionNext 𝒜) n st

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_fusionStates_chosen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_fusionStates_chosen
  (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (hst : st.chosen = []) :
  ∀ n, (rosenthalFusionStates 𝒜 st n).chosen =
    rosenthalInitialSegment (rosenthalFusionPoints 𝒜 st) n := by
  intro n
  induction n with
  | zero => exact hst
  | succ n ih =>
    rw [rosenthal_fusionStates_succ]
    change (rosenthalFusionStates 𝒜 st n).chosen ++
      [rosenthalFusionPoints 𝒜 st n] = _
    rw [ih]
    simp [rosenthalInitialSegment, List.range_succ]

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_fusionPoints_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_fusionPoints_strictMono
  (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
  StrictMono (rosenthalFusionPoints 𝒜 st) := by
  apply strictMono_nat_of_lt_succ
  intro n
  let cur := rosenthalFusionStates 𝒜 st n
  let step := rosenthalFusionStep 𝒜 cur
  have hstate : rosenthalFusionStates 𝒜 st (n + 1) = rosenthalFusionNext 𝒜 cur :=
    rosenthal_fusionStates_succ 𝒜 st n
  have hmem := (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st (n + 1))).point_mem
  rw [hstate] at hmem
  obtain ⟨j, hj⟩ := hmem
  change step.point <
    (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st (n + 1))).point
  rw [hstate, ← hj]
  exact step.above j

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_range_fusionState_tail_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_range_fusionState_tail_subset
  (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
  ∀ n, Set.range (rosenthalFusionStates 𝒜 st n).tail ⊆ Set.range st.tail := by
  intro n
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    rw [rosenthal_fusionStates_succ]
    exact (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).tail_subset.trans ih

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_range_fusionPoints_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_range_fusionPoints_subset
  (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
  Set.range (rosenthalFusionPoints 𝒜 st) ⊆ Set.range st.tail := by
  rintro _ ⟨n, rfl⟩
  apply rosenthal_range_fusionState_tail_subset 𝒜 st n
  exact (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).point_mem

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_initialSegment_comp_sublist](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_initialSegment_comp_sublist
  (φ : ℕ → ℕ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
  ∀ n, (rosenthalInitialSegment (φ ∘ ψ) n).Sublist
    (rosenthalInitialSegment φ (ψ n)) := by
  intro n
  induction n with
  | zero => exact List.nil_sublist _
  | succ n ih =>
    have hleft : rosenthalInitialSegment (φ ∘ ψ) (n + 1) =
      rosenthalInitialSegment (φ ∘ ψ) n ++ [φ (ψ n)] := by
      simp [rosenthalInitialSegment, List.range_succ, Function.comp_def]
    rw [hleft]
    have h₁ := ih.append_right [φ (ψ n)]
    have hmiddle : rosenthalInitialSegment φ (ψ n) ++ [φ (ψ n)] =
      rosenthalInitialSegment φ (ψ n + 1) := by
      simp [rosenthalInitialSegment, List.range_succ]
    rw [hmiddle] at h₁
    have hbound : ψ n + 1 ≤ ψ (n + 1) := Nat.succ_le_of_lt (hψ (Nat.lt_succ_self n))
    have h₂ : (rosenthalInitialSegment φ (ψ n + 1)).Sublist
      (rosenthalInitialSegment φ (ψ (n + 1))) := by
      exact (List.range_sublist.mpr hbound).map φ
    exact h₁.trans h₂

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_exists_finite_pair_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_exists_finite_pair_obstruction
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
  (R : K → ℕ → ℕ → Prop) (hclosed : ∀ i j, IsClosed {k | R k i j})
  (φ : ℕ → ℕ) (h : ¬∃ k, ∀ n, R k (φ (2 * n)) (φ (2 * n + 1))) :
  ∃ N, ¬∃ k, ∀ n < N, R k (φ (2 * n)) (φ (2 * n + 1)) := by
  let U : ℕ → Set K := fun n => {k | ¬R k (φ (2 * n)) (φ (2 * n + 1))}
  have hopen : ∀ n, IsOpen (U n) := by
    intro n
    exact (hclosed _ _).isOpen_compl
  have hcover : Set.univ ⊆ ⋃ n, U n := by
    intro k hk
    rw [Set.mem_iUnion]
    by_contra hnone
    push Not at hnone
    have hall : ∀ n, R k (φ (2 * n)) (φ (2 * n + 1)) := by
      intro n
      simpa only [U, Set.mem_ofPred_eq, not_not] using hnone n
    exact h ⟨k, hall⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨t.sup id + 1, ?_⟩
  rintro ⟨k, hk⟩
  have hkt := ht (Set.mem_univ k)
  simp only [Set.mem_iUnion] at hkt
  obtain ⟨n, hnmem, hnU⟩ := hkt
  have hnlt : n < t.sup id + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hnmem)
  exact hnU (hk n hnlt)

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_pairLift_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_pairLift_even (η : ℕ → ℕ) (n : ℕ) :
  rosenthalPairLift η (2 * n) = 2 * η n := by
  have hdiv : 2 * n / 2 = n := by omega
  have hmod : 2 * n % 2 = 0 := by omega
  simp only [rosenthalPairLift, hdiv, hmod, add_zero]

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_pairLift_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_pairLift_odd (η : ℕ → ℕ) (n : ℕ) :
  rosenthalPairLift η (2 * n + 1) = 2 * η n + 1 := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp only [rosenthalPairLift, hdiv, hmod]

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_pairLift_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_pairLift_strictMono
  {η : ℕ → ℕ} (hη : StrictMono η) : StrictMono (rosenthalPairLift η) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [rosenthal_pairLift_even, rosenthal_pairLift_odd]
    omega
  · rw [rosenthal_pairLift_odd,
    show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
    rosenthal_pairLift_even]
    have h : η k < η (k + 1) := by simpa using hη (Nat.lt_succ_self k)
    omega

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_exists_finite_scalar_net](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_exists_finite_scalar_net
  {𝕜 : Type*} [RCLike 𝕜] (B δ : ℝ) (hδ : 0 < δ) :
  ∃ t : Finset 𝕜, ∀ z : 𝕜, ‖z‖ ≤ B → ∃ u ∈ t, dist z u ≤ δ := by
  have hcover : Metric.closedBall (0 : 𝕜) B ⊆ ⋃ u, Metric.ball u δ := by
    intro z hz
    rw [Set.mem_iUnion]
    exact ⟨z, Metric.mem_ball_self hδ⟩
  obtain ⟨t, ht⟩ := (ProperSpace.isCompact_closedBall (0 : 𝕜) B).elim_finite_subcover
    (fun u => Metric.ball u δ) (fun _ => Metric.isOpen_ball) hcover
  refine ⟨t, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.closedBall (0 : 𝕜) B := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hzt := ht hzball
  simp only [Set.mem_iUnion] at hzt
  obtain ⟨u, hut, hzu⟩ := hzt
  exact ⟨u, hut, (Metric.mem_ball.mp hzu).le⟩

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_assignmentIndices_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_assignmentIndices_even (P : Finset ℕ) (n : ℕ) :
  rosenthalAssignmentIndices P (2 * n) =
    if n ∈ P then 3 * n + 1 else 3 * n := by
  have hdiv : 2 * n / 2 = n := by omega
  have hmod : 2 * n % 2 = 0 := by omega
  simp [rosenthalAssignmentIndices, hdiv, hmod]

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_assignmentIndices_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_assignmentIndices_odd (P : Finset ℕ) (n : ℕ) :
  rosenthalAssignmentIndices P (2 * n + 1) =
    if n ∈ P then 3 * n + 2 else 3 * n + 1 := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp [rosenthalAssignmentIndices, hdiv, hmod]

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_assignmentIndices_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_assignmentIndices_strictMono (P : Finset ℕ) :
  StrictMono (rosenthalAssignmentIndices P) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [rosenthal_assignmentIndices_even, rosenthal_assignmentIndices_odd]
    split <;> omega
  · rw [rosenthal_assignmentIndices_odd,
    show 2 * i + 1 + 1 = 2 * (i + 1) by omega,
    rosenthal_assignmentIndices_even]
    split <;> split <;> omega

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_cell_pair_assignments](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_cell_pair_assignments
  {K 𝕜 : Type*} [PseudoMetricSpace 𝕜]
  (f : ℕ → K → 𝕜) (delta : ℝ) (u v : 𝕜)
  {φ : ℕ → ℕ} (hφ : StrictMono φ)
  (hall : ∀ θ : ℕ → ℕ, StrictMono θ →
    rosenthalPaired (rosenthalCellPair f delta u v) (φ ∘ θ)) :
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
    ∀ P Q : Finset ℕ, Disjoint P Q → ∃ k : K,
      (∀ i ∈ P, dist (f (ψ i) k) u ≤ delta) ∧
        ∀ i ∈ Q, dist (f (ψ i) k) v ≤ delta := by
  classical
  let sparse : ℕ → ℕ := fun n => 3 * n + 1
  have hsparse : StrictMono sparse := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [sparse]
    omega
  refine ⟨φ ∘ sparse, hφ.comp hsparse, Set.range_comp_subset_range sparse φ, ?_⟩
  intro P Q hPQ
  obtain ⟨k, hk⟩ := hall (rosenthalAssignmentIndices P)
    (rosenthal_assignmentIndices_strictMono P)
  refine ⟨k, ?_, ?_⟩
  · intro i hi
    have hpair := (hk i).1
    simpa [rosenthalCellPair, Function.comp_def, sparse,
      rosenthal_assignmentIndices_even, hi] using hpair
  · intro i hi
    have hnot : i ∉ P := by
      intro hip
      exact Finset.disjoint_left.mp hPQ hip hi
    have hpair := (hk i).2
    simpa [rosenthalCellPair, Function.comp_def, sparse,
      rosenthal_assignmentIndices_odd, hnot] using hpair

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_norm_le_abs_re_add_abs_im](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_norm_le_abs_re_add_abs_im
  {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
  ‖z‖ ≤ |RCLike.re z| + |RCLike.im z| := by
  rw [← RCLike.re_add_im z]
  refine (norm_add_le _ _).trans ?_
  rw [RCLike.norm_ofReal, norm_mul, RCLike.norm_ofReal, RCLike.norm_I]
  split <;> simp [abs_nonneg]

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_exists_large_quadrant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_exists_large_quadrant
  {𝕜 : Type*} [RCLike 𝕜] (s : Finset ℕ) (z : ℕ → 𝕜) :
  ∃ P : Finset ℕ, P ⊆ s ∧
    (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ P, z i‖ := by
  classical
  let rp := s.filter fun i => 0 ≤ RCLike.re (z i)
  let rn := s.filter fun i => ¬0 ≤ RCLike.re (z i)
  let ip := s.filter fun i => 0 ≤ RCLike.im (z i)
  let inn := s.filter fun i => ¬0 ≤ RCLike.im (z i)
  have hrp : (∑ i ∈ rp, |RCLike.re (z i)|) ≤ ‖∑ i ∈ rp, z i‖ := by
    calc
      (∑ i ∈ rp, |RCLike.re (z i)|) = ∑ i ∈ rp, RCLike.re (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_nonneg (Finset.mem_filter.mp hi).2
      _ = RCLike.re (∑ i ∈ rp, z i) := by
        symm
        exact map_sum RCLike.re _ _
      _ ≤ ‖∑ i ∈ rp, z i‖ := RCLike.re_le_norm _
  have hrn : (∑ i ∈ rn, |RCLike.re (z i)|) ≤ ‖∑ i ∈ rn, z i‖ := by
    calc
      (∑ i ∈ rn, |RCLike.re (z i)|) = ∑ i ∈ rn, -RCLike.re (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ = -RCLike.re (∑ i ∈ rn, z i) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        exact (map_sum (RCLike.re : 𝕜 →+ ℝ) z rn).symm
      _ ≤ ‖∑ i ∈ rn, z i‖ := by
        simpa only [map_neg, norm_neg] using RCLike.re_le_norm (-(∑ i ∈ rn, z i))
  have hip : (∑ i ∈ ip, |RCLike.im (z i)|) ≤ ‖∑ i ∈ ip, z i‖ := by
    calc
      (∑ i ∈ ip, |RCLike.im (z i)|) = ∑ i ∈ ip, RCLike.im (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_nonneg (Finset.mem_filter.mp hi).2
      _ = RCLike.im (∑ i ∈ ip, z i) := by
        symm
        exact map_sum RCLike.im _ _
      _ ≤ ‖∑ i ∈ ip, z i‖ := RCLike.im_le_norm _
  have hinn : (∑ i ∈ inn, |RCLike.im (z i)|) ≤ ‖∑ i ∈ inn, z i‖ := by
    calc
      (∑ i ∈ inn, |RCLike.im (z i)|) = ∑ i ∈ inn, -RCLike.im (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ = -RCLike.im (∑ i ∈ inn, z i) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        exact (map_sum (RCLike.im : 𝕜 →+ ℝ) z inn).symm
      _ ≤ ‖∑ i ∈ inn, z i‖ := by
        simpa only [map_neg, norm_neg] using RCLike.im_le_norm (-(∑ i ∈ inn, z i))
  have hre : (∑ i ∈ s, |RCLike.re (z i)|) ≤
    ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun i => 0 ≤ RCLike.re (z i)) (fun i => |RCLike.re (z i)|)]
    change (∑ i ∈ rp, |RCLike.re (z i)|) + (∑ i ∈ rn, |RCLike.re (z i)|) ≤ _
    exact add_le_add hrp hrn
  have him : (∑ i ∈ s, |RCLike.im (z i)|) ≤
    ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun i => 0 ≤ RCLike.im (z i)) (fun i => |RCLike.im (z i)|)]
    change (∑ i ∈ ip, |RCLike.im (z i)|) + (∑ i ∈ inn, |RCLike.im (z i)|) ≤ _
    exact add_le_add hip hinn
  have htotal : (∑ i ∈ s, ‖z i‖) ≤
    ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ +
      ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ := by
    have hcoord : (∑ i ∈ s, ‖z i‖) ≤
      (∑ i ∈ s, |RCLike.re (z i)|) +
        ∑ i ∈ s, |RCLike.im (z i)| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => rosenthal_norm_le_abs_re_add_abs_im (z i)
    linarith
  by_cases h : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ rp, z i‖
  · exact ⟨rp, Finset.filter_subset _ _, h⟩
  by_cases h' : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ rn, z i‖
  · exact ⟨rn, Finset.filter_subset _ _, h'⟩
  by_cases h'' : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ ip, z i‖
  · exact ⟨ip, Finset.filter_subset _ _, h''⟩
  refine ⟨inn, Finset.filter_subset _ _, ?_⟩
  by_contra h'''
  push Not at h h' h'' h'''
  linarith

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_dualBallStrong_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_dualBallStrong_norm_le
  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (g : RosenthalDualBall 𝕜 E) : ‖rosenthalDualBallStrong g‖ ≤ 1 := by
  simpa [rosenthalDualBallStrong, Metric.mem_closedBall, dist_eq_norm] using g.2

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_dualEval_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_dualEval_continuous
  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (x : ℕ → E) (n : ℕ) : Continuous (rosenthalDualEval (𝕜 := 𝕜) x n) :=
  (WeakDual.eval_continuous (x n)).comp continuous_subtype_val

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_dualEval_eq_strong](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_dualEval_eq_strong
  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (x : ℕ → E) (n : ℕ) (g : RosenthalDualBall 𝕜 E) :
  rosenthalDualEval (𝕜 := 𝕜) x n g =
    rosenthalDualBallStrong (𝕜 := 𝕜) g (x n) :=
(WeakDual.toStrongDual_apply g.1 (x n)).symm

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_dual_sum_error](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_dual_sum_error
  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (y : ℕ → E) (u v : 𝕜) (delta : ℝ)
  (a : ℕ →₀ 𝕜) (P : Finset ℕ) (hP : P ⊆ a.support)
  (g h : RosenthalDualBall 𝕜 E)
  (hgu : ∀ i ∈ a.support \ P,
    dist (rosenthalDualEval (𝕜 := 𝕜) y i g) u ≤ delta)
  (hgv : ∀ i ∈ P,
    dist (rosenthalDualEval (𝕜 := 𝕜) y i g) v ≤ delta)
  (hhu : ∀ i ∈ a.support,
    dist (rosenthalDualEval (𝕜 := 𝕜) y i h) u ≤ delta) :
  ‖rosenthalDualBallStrong g (∑ i ∈ a.support, a i • y i) -
    rosenthalDualBallStrong h (∑ i ∈ a.support, a i • y i) -
      ∑ i ∈ P, a i * (v - u)‖ ≤
    2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
  classical
  let F := rosenthalDualBallStrong g
  let G := rosenthalDualBallStrong h
  let target : ℕ → 𝕜 := fun i => if i ∈ P then v - u else 0
  have herr : ∀ i ∈ a.support,
    ‖(F (y i) - G (y i)) - target i‖ ≤ 2 * delta := by
    intro i hi
    by_cases hiP : i ∈ P
    · have hFv : ‖F (y i) - v‖ ≤ delta := by
      simpa [F, dist_eq_norm, rosenthal_dualEval_eq_strong] using hgv i hiP
      have hGu : ‖G (y i) - u‖ ≤ delta := by
        simpa [G, dist_eq_norm, rosenthal_dualEval_eq_strong] using hhu i hi
      rw [show target i = v - u by simp [target, hiP]]
      rw [show (F (y i) - G (y i)) - (v - u) =
        (F (y i) - v) - (G (y i) - u) by ring]
      exact (norm_sub_le _ _).trans (by linarith)
    · have hiDiff : i ∈ a.support \ P := Finset.mem_sdiff.mpr ⟨hi, hiP⟩
      have hFu : ‖F (y i) - u‖ ≤ delta := by
        simpa [F, dist_eq_norm, rosenthal_dualEval_eq_strong] using hgu i hiDiff
      have hGu : ‖G (y i) - u‖ ≤ delta := by
        simpa [G, dist_eq_norm, rosenthal_dualEval_eq_strong] using hhu i hi
      rw [show target i = 0 by simp [target, hiP], sub_zero]
      rw [show F (y i) - G (y i) = (F (y i) - u) - (G (y i) - u) by ring]
      exact (norm_sub_le _ _).trans (by linarith)
  have hsum : ‖∑ i ∈ a.support,
    a i * ((F (y i) - G (y i)) - target i)‖ ≤
    2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
    calc
      ‖∑ i ∈ a.support, a i * ((F (y i) - G (y i)) - target i)‖ ≤
        ∑ i ∈ a.support, ‖a i * ((F (y i) - G (y i)) - target i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ a.support, ‖a i‖ * (2 * delta) := by
        exact Finset.sum_le_sum fun i hi => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (herr i hi) (norm_nonneg _)
      _ = 2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have htarget : (∑ i ∈ a.support, a i * target i) =
    ∑ i ∈ P, a i * (v - u) := by
    calc
      (∑ i ∈ a.support, a i * target i) = ∑ i ∈ P, a i * target i := by
        symm
        exact Finset.sum_subset hP fun i hi hiP => by simp [target, hiP]
      _ = ∑ i ∈ P, a i * (v - u) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [target, hi]
  have heq :
    F (∑ i ∈ a.support, a i • y i) -
      G (∑ i ∈ a.support, a i • y i) -
        ∑ i ∈ P, a i * (v - u) =
      ∑ i ∈ a.support, a i * ((F (y i) - G (y i)) - target i) := by
    rw [map_sum, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, ← htarget, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change ‖F (∑ i ∈ a.support, a i • y i) -
    G (∑ i ∈ a.support, a i • y i) -
      ∑ i ∈ P, a i * (v - u)‖ ≤ _
  rwa [heq]

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_uniform_lower_bound_of_assignments](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_uniform_lower_bound_of_assignments
  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (y : ℕ → E) (epsilon : ℝ) (hepsilon : 0 < epsilon) (u v : 𝕜)
  (hcenters : epsilon ≤ dist u v + 2 * (epsilon / 64))
  (hassign : ∀ P Q : Finset ℕ, Disjoint P Q →
    ∃ g : RosenthalDualBall 𝕜 E,
      (∀ i ∈ P,
        dist (rosenthalDualEval (𝕜 := 𝕜) y i g) u ≤ epsilon / 64) ∧
      ∀ i ∈ Q,
        dist (rosenthalDualEval (𝕜 := 𝕜) y i g) v ≤ epsilon / 64) :
  HasUniformL1LowerBound (𝕜 := 𝕜) y := by
  refine ⟨epsilon / 16, by positivity, ?_⟩
  intro a
  let total : ℝ := ∑ i ∈ a.support, ‖a i‖
  let S : E := ∑ i ∈ a.support, a i • y i
  obtain ⟨P, hP, hquadrant⟩ := rosenthal_exists_large_quadrant a.support
    (fun i => a i * (v - u))
  obtain ⟨g, hgu, hgv⟩ := hassign (a.support \ P) P Finset.sdiff_disjoint
  obtain ⟨h, hhu, _⟩ := hassign a.support ∅ (by simp)
  let F := rosenthalDualBallStrong g
  let G := rosenthalDualBallStrong h
  let Z : 𝕜 := ∑ i ∈ P, a i * (v - u)
  have herror : ‖F S - G S - Z‖ ≤ 2 * (epsilon / 64) * total := by
    simpa [F, G, S, Z, total] using
      rosenthal_dual_sum_error y u v (epsilon / 64) a P hP g h hgu hgv hhu
  have hF : ‖F S‖ ≤ ‖S‖ := by
    calc
      ‖F S‖ ≤ ‖F‖ * ‖S‖ := ContinuousLinearMap.le_opNorm F S
      _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right
        (rosenthal_dualBallStrong_norm_le g) (norm_nonneg _)
      _ = ‖S‖ := one_mul _
  have hG : ‖G S‖ ≤ ‖S‖ := by
    calc
      ‖G S‖ ≤ ‖G‖ * ‖S‖ := ContinuousLinearMap.le_opNorm G S
      _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right
        (rosenthal_dualBallStrong_norm_le h) (norm_nonneg _)
      _ = ‖S‖ := one_mul _
  have hdiff : ‖F S - G S‖ ≤ 2 * ‖S‖ :=
    (norm_sub_le _ _).trans (by linarith)
  have htriangle : ‖Z‖ ≤ ‖F S - G S - Z‖ + ‖F S - G S‖ := by
    calc
      ‖Z‖ = ‖(Z - (F S - G S)) + (F S - G S)‖ := by congr 1; ring
      _ ≤ ‖Z - (F S - G S)‖ + ‖F S - G S‖ := norm_add_le _ _
      _ = ‖F S - G S - Z‖ + ‖F S - G S‖ := by rw [norm_sub_rev]
  have hZupper : ‖Z‖ ≤ 2 * (epsilon / 64) * total + 2 * ‖S‖ :=
    htriangle.trans (add_le_add herror hdiff)
  have hnormsum : (∑ i ∈ a.support, ‖a i * (v - u)‖) = dist u v * total := by
    simp only [norm_mul]
    rw [← Finset.sum_mul]
    simp [total, dist_eq_norm, norm_sub_rev, mul_comm]
  have hZlower : dist u v * total / 4 ≤ ‖Z‖ := by
    rw [hnormsum] at hquadrant
    simpa [Z] using hquadrant
  have htotal : 0 ≤ total := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcenter' : epsilon - 2 * (epsilon / 64) ≤ dist u v := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hcenter' htotal
  change epsilon / 16 * total ≤ ‖S‖
  nlinarith

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_dualEval_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_dualEval_bounded
  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x)) :
  ∃ B : ℝ, ∀ n (g : RosenthalDualBall 𝕜 E),
    ‖rosenthalDualEval (𝕜 := 𝕜) x n g‖ ≤ B := by
  obtain ⟨B, hB⟩ := hx.subset_closedBall 0
  refine ⟨B, ?_⟩
  intro n g
  have hxn : ‖x n‖ ≤ B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hB ⟨n, rfl⟩
  calc
    ‖rosenthalDualEval (𝕜 := 𝕜) x n g‖ =
      ‖rosenthalDualBallStrong g (x n)‖ := by
      rw [rosenthal_dualEval_eq_strong]
    _ ≤ ‖rosenthalDualBallStrong g‖ * ‖x n‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x n‖ := mul_le_mul_of_nonneg_right
      (rosenthal_dualBallStrong_norm_le g) (norm_nonneg _)
    _ ≤ B := by simpa using hxn

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_weakCauchy_of_dualBall](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_weakCauchy_of_dualBall
  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (x : ℕ → E) (φ : ℕ → ℕ)
  (h : ∀ g : RosenthalDualBall 𝕜 E, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N, ∀ m n, N ≤ m → N ≤ n →
      dist (rosenthalDualEval (𝕜 := 𝕜) x (φ m) g)
        (rosenthalDualEval (𝕜 := 𝕜) x (φ n) g) < epsilon) :
  ∀ (f : E →L[𝕜] 𝕜) (epsilon : ℝ), 0 < epsilon →
    ∃ N, ∀ m n, N ≤ m → N ≤ n →
      ‖f (x (φ m)) - f (x (φ n))‖ < epsilon := by
  intro f epsilon hepsilon
  by_cases hf : f = 0
  · subst f
    exact ⟨0, fun _ _ _ _ => by simpa using hepsilon⟩
  · have hfnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
    let c : 𝕜 := ((‖f‖⁻¹ : ℝ) : 𝕜)
    let f' : E →L[𝕜] 𝕜 := c • f
    have hcnorm : ‖c‖ = ‖f‖⁻¹ := by
      simp [c]
    have hf'norm : ‖f'‖ ≤ 1 := by
      change ‖c • f‖ ≤ 1
      rw [norm_smul, hcnorm, inv_mul_cancel₀ (ne_of_gt hfnorm)]
    let g : RosenthalDualBall 𝕜 E :=
      ⟨StrongDual.toWeakDual f', by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hf'norm⟩
    have hepsdiv : 0 < epsilon / ‖f‖ := div_pos hepsilon hfnorm
    obtain ⟨N, hN⟩ := h g (epsilon / ‖f‖) hepsdiv
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hclose := hN m n hm hn
    change dist ((StrongDual.toWeakDual f') (x (φ m)))
      ((StrongDual.toWeakDual f') (x (φ n))) < epsilon / ‖f‖ at hclose
    rw [StrongDual.toWeakDual_apply, StrongDual.toWeakDual_apply] at hclose
    have hscaled : ‖f‖⁻¹ * ‖f (x (φ m)) - f (x (φ n))‖ < epsilon / ‖f‖ := by
      change dist (c * f (x (φ m))) (c * f (x (φ n))) < epsilon / ‖f‖ at hclose
      rwa [dist_eq_norm, ← mul_sub, norm_mul, hcnorm] at hclose
    have hmul := mul_lt_mul_of_pos_left hscaled hfnorm
    calc
      ‖f (x (φ m)) - f (x (φ n))‖ =
        ‖f‖ * (‖f‖⁻¹ * ‖f (x (φ m)) - f (x (φ n))‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hfnorm), one_mul]
      _ < ‖f‖ * (epsilon / ‖f‖) := hmul
      _ = epsilon := by
        rw [div_eq_mul_inv]
        calc
          ‖f‖ * (epsilon * ‖f‖⁻¹) = epsilon * (‖f‖ * ‖f‖⁻¹) := by ring
          _ = epsilon := by rw [mul_inv_cancel₀ (ne_of_gt hfnorm), mul_one]

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_exists_paired_subsequence_of_not_eventually_close](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_exists_paired_subsequence_of_not_eventually_close
  {α : Type*} [PseudoMetricSpace α] (u : ℕ → α) {ε : ℝ} (hε : 0 < ε)
  (h : ¬∃ N, ∀ m n, N ≤ m → N ≤ n → dist (u m) (u n) < ε) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ j, ε ≤ dist (u (φ (2 * j))) (u (φ (2 * j + 1))) := by
  push Not at h
  have hpick : ∀ N : ℕ, ∃ a b : ℕ,
    N ≤ a ∧ a < b ∧ ε ≤ dist (u a) (u b) := by
    intro N
    obtain ⟨m, n, hm, hn, hmn⟩ := h N
    have hne : m ≠ n := by
      intro heq
      subst n
      simpa using (lt_of_lt_of_le hε hmn).ne'
    obtain hlt | hgt := lt_or_gt_of_ne hne
    · exact ⟨m, n, hm, hlt, hmn⟩
    · exact ⟨n, m, hn, hgt, by simpa [dist_comm] using hmn⟩
  choose lo hi hlo hlthi hgap using hpick
  let next : ℕ → ℕ := fun N => hi N + 1
  let bound : ℕ → ℕ := fun n => next^[n] 0
  let left : ℕ → ℕ := fun n => lo (bound n)
  let right : ℕ → ℕ := fun n => hi (bound n)
  let φ : ℕ → ℕ := fun n =>
    if n % 2 = 0 then left (n / 2) else right (n / 2)
  have hbound_succ : ∀ n, bound (n + 1) = right n + 1 := by
    intro n
    rw [show n + 1 = n.succ from rfl]
    exact Function.iterate_succ_apply' next n 0
  have hφeven : ∀ n, φ (2 * n) = left n := by
    intro n
    have hdiv : 2 * n / 2 = n := by omega
    have hmod : 2 * n % 2 = 0 := by omega
    simp only [φ, hdiv, hmod, ↓reduceIte]
  have hφodd : ∀ n, φ (2 * n + 1) = right n := by
    intro n
    have hdiv : (2 * n + 1) / 2 = n := by omega
    have hmod : (2 * n + 1) % 2 = 1 := by omega
    simp only [φ, hdiv, hmod, one_ne_zero, ↓reduceIte]
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [hφeven, hφodd]
      exact hlthi _
    · rw [hφodd, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, hφeven]
      have hnext : right k + 1 ≤ left (k + 1) := by
        rw [← hbound_succ]
        exact hlo _
      omega
  exact ⟨φ, hφ, fun j => by rw [hφeven, hφodd]; exact hgap _⟩

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[rosenthal_eventually_close_of_no_gap_paired](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_eventually_close_of_no_gap_paired
  {K α : Type*} [PseudoMetricSpace α] (f : ℕ → K → α) {ε : ℝ} (hε : 0 < ε)
  {φ : ℕ → ℕ}
  (hno : ∀ θ : ℕ → ℕ, StrictMono θ →
    ¬rosenthalPaired (rosenthalGap f ε) (φ ∘ θ)) :
  ∀ k : K, ∃ N, ∀ m n, N ≤ m → N ≤ n →
    dist (f (φ m) k) (f (φ n) k) < ε := by
  intro k
  by_contra hclose
  obtain ⟨θ, hθ, hgap⟩ :=
    rosenthal_exists_paired_subsequence_of_not_eventually_close
      (fun n => f (φ n) k) hε hclose
  apply hno θ hθ
  exact ⟨k, fun j => by simpa [rosenthalGap, Function.comp_def] using hgap j⟩

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

/--
[RosenthalL1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_l1_eq
-- given
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (x : ℕ → E)
  (hx : Bornology.IsBounded (Set.range x)) :
-- imply
  ∃ (φ : ℕ → ℕ) (_ : StrictMono φ),
    (∀ (f : E →L[𝕜] 𝕜) (ε : ℝ), 0 < ε →
      ∃ N, ∀ m n, N ≤ m → N ≤ n → ‖f (x (φ m)) - f (x (φ n))‖ < ε) ∨
    HasUniformL1LowerBound (𝕜 := 𝕜) (x ∘ φ) := by
-- proof
  apply rosenthal_l1 x hx


-- created on 2026-10-10
-- updated on 2026-10-26
