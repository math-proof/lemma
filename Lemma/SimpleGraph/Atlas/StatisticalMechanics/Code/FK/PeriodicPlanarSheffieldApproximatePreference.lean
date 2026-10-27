import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldApproximatePreference.Part2
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_common_approximate_preference_grid_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma exists_common_approximate_preference_grid_witness_eq
  {n m : Nat}
  {epsilon : Real}
  {bottom top left right : PreferenceGridVertex n m → Real}
-- given
  (hn : 0 < n)
  (hepsilon : 0 ≤ epsilon)
  (hbottom : ∀ i : Fin (n + 1), top (i, 0) ≤ bottom (i, 0) + epsilon)
  (htop : ∀ i : Fin (n + 1), bottom (i, Fin.last m) + epsilon < top (i, Fin.last m))
  (hleft : ∀ j : Fin (m + 1), right (0, j) ≤ left (0, j) + epsilon)
  (hright : ∀ j : Fin (m + 1), left (Fin.last n, j) + epsilon < right (Fin.last n, j)) :
-- imply
  ∃ x xVertical xHorizontal : PreferenceGridVertex n m, top x ≤ bottom x + epsilon ∧ right x ≤ left x + epsilon ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧ bottom xVertical ≤ top xVertical + epsilon ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧ left xHorizontal ≤ right xHorizontal + epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_common_approximate_preference_grid_witness hn epsilon hepsilon bottom top left right hbottom htop hleft hright

/--
[exists_common_weak_approximate_preference_grid_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma exists_common_weak_approximate_preference_grid_witness_eq
  {n m : Nat}
  {epsilon : Real}
  {bottom top left right : PreferenceGridVertex n m → Real}
-- given
  (hn : 0 < n)
  (hm : 0 < m)
  (hepsilon : 0 ≤ epsilon)
  (hbottom : ∀ i : Fin (n + 1), top (i, 0) ≤ bottom (i, 0) + epsilon)
  (htop : ∀ i : Fin (n + 1), bottom (i, Fin.last m) ≤ top (i, Fin.last m) + epsilon)
  (hleft : ∀ j : Fin (m + 1), right (0, j) ≤ left (0, j) + epsilon)
  (hright : ∀ j : Fin (m + 1), left (Fin.last n, j) ≤ right (Fin.last n, j) + epsilon) :
-- imply
  ∃ x xVertical xHorizontal : PreferenceGridVertex n m, top x ≤ bottom x + epsilon ∧ right x ≤ left x + epsilon ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧ bottom xVertical ≤ top xVertical + epsilon ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧ left xHorizontal ≤ right xHorizontal + epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_common_weak_approximate_preference_grid_witness hn hm epsilon hepsilon bottom top left right hbottom htop hleft hright

/--
[rectangleEndpointPreferenceError_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma rectangleEndpointPreferenceError_nonneg_eq
  {n m : Nat}
  {bottom top left right : PreferenceGridVertex n m → Real} :
-- imply
  0 ≤ rectangleEndpointPreferenceError bottom top left right := by
-- proof
  apply StatMech.FK.PeriodicPlanar.rectangleEndpointPreferenceError_nonneg bottom top left right

/--
[rectangleEndpointPreferenceError_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma rectangleEndpointPreferenceError_bounds_eq
  {n m : Nat}
  {bottom top left right : PreferenceGridVertex n m → Real} :
-- imply
  (∀ i : Fin (n + 1), top (i, 0) ≤ bottom (i, 0) + rectangleEndpointPreferenceError bottom top left right) ∧ (∀ i : Fin (n + 1), bottom (i, Fin.last m) ≤ top (i, Fin.last m) + rectangleEndpointPreferenceError bottom top left right) ∧ (∀ j : Fin (m + 1), right (0, j) ≤ left (0, j) + rectangleEndpointPreferenceError bottom top left right) ∧ ∀ j : Fin (m + 1), left (Fin.last n, j) ≤ right (Fin.last n, j) + rectangleEndpointPreferenceError bottom top left right := by
-- proof
  apply StatMech.FK.PeriodicPlanar.rectangleEndpointPreferenceError_bounds bottom top left right

/--
[rectangleEndpointPreferenceError_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma rectangleEndpointPreferenceError_tendsto_zero_eq
  {n m : Nat}
  {bottom top left right : Nat → PreferenceGridVertex n m → Real}
-- given
  (hbottomOne : ∀ i : Fin (n + 1), Tendsto (fun N => bottom N (i, 0)) atTop (nhds 1))
  (htopOne : ∀ i : Fin (n + 1), Tendsto (fun N => top N (i, Fin.last m)) atTop (nhds 1))
  (hleftOne : ∀ j : Fin (m + 1), Tendsto (fun N => left N (0, j)) atTop (nhds 1))
  (hrightOne : ∀ j : Fin (m + 1), Tendsto (fun N => right N (Fin.last n, j)) atTop (nhds 1))
  (hbottomLe : ∀ N x, bottom N x ≤ 1)
  (htopLe : ∀ N x, top N x ≤ 1)
  (hleftLe : ∀ N x, left N x ≤ 1)
  (hrightLe : ∀ N x, right N x ≤ 1) :
-- imply
  Tendsto (fun N => rectangleEndpointPreferenceError (bottom N) (top N) (left N) (right N)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.rectangleEndpointPreferenceError_tendsto_zero bottom top left right hbottomOne htopOne hleftOne hrightOne hbottomLe htopLe hleftLe hrightLe

/--
[PeriodicPlaneEmbedding.preference_max_bottom_left_add_epsilon_ge_fourthRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma preference_max_bottom_left_add_epsilon_ge_fourthRoot_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hepsilon : 0 ≤ epsilon)
  (hS : S ⊆ E.rectVertices a b c d)
  (hBottomTop : mu.real (E.rectSideConnectionEvent a b c d S (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d)) + epsilon)
  (hLeftRight : mu.real (E.rectSideConnectionEvent a b c d S (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d)) + epsilon) :
-- imply
  1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤ max (mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d))) (mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d))) + epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preference_max_bottom_left_add_epsilon_ge_fourthRoot E mu hFKG a b c d S epsilon hepsilon hS hBottomTop hLeftRight

/--
[PeriodicPlaneEmbedding.verticalCrossing_ge_approxPreferredSide_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma verticalCrossing_ge_approxPreferredSide_transfer_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hOpposite : mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectTopBoundaryVertices a b c d)) + epsilon) :
-- imply
  let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectBottomBoundaryVertices a b c d)) let H := mu.real (P.setHitsInfinite (R : Set V)) let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R) A * (H * A - M - epsilon) - M ≤ mu.real (E.verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_ge_approxPreferredSide_transfer E mu hFKG a b c d L R epsilon hOpposite

/--
[PeriodicPlaneEmbedding.horizontalCrossing_ge_approxPreferredSide_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma horizontalCrossing_ge_approxPreferredSide_transfer_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hOpposite : mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectRightBoundaryVertices a b c d)) + epsilon) :
-- imply
  let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectLeftBoundaryVertices a b c d)) let H := mu.real (P.setHitsInfinite (R : Set V)) let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R) A * (H * A - M - epsilon) - M ≤ mu.real (E.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_ge_approxPreferredSide_transfer E mu hFKG a b c d L R epsilon hOpposite

/--
[PeriodicPlaneEmbedding.exists_approxPreferredSide_crossing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma exists_approxPreferredSide_crossing_branch_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {n m : Nat}
  {epsilon : Real}
  {source : PreferenceGridVertex n m → Finset V}
  {bottom top left right : PreferenceGridVertex n m → Real}
-- given
  (hFKG : IsFKG mu)
  (hn : 0 < n)
  (hm : 0 < m)
  (hepsilon : 0 ≤ epsilon)
  (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a b c d)
  (hbottomScore : ∀ x, bottom x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectBottomBoundaryVertices a b c d)))
  (htopScore : ∀ x, top x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectTopBoundaryVertices a b c d)))
  (hleftScore : ∀ x, left x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectLeftBoundaryVertices a b c d)))
  (hrightScore : ∀ x, right x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectRightBoundaryVertices a b c d)))
  (hbottom : ∀ i : Fin (n + 1), top (i, 0) ≤ bottom (i, 0) + epsilon)
  (htop : ∀ i : Fin (n + 1), bottom (i, Fin.last m) ≤ top (i, Fin.last m) + epsilon)
  (hleft : ∀ j : Fin (m + 1), right (0, j) ≤ left (0, j) + epsilon)
  (hright : ∀ j : Fin (m + 1), left (Fin.last n, j) ≤ right (Fin.last n, j) + epsilon) :
-- imply
  ∃ x xVertical xHorizontal : PreferenceGridVertex n m, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧ ((1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ bottom x + epsilon ∧ bottom x * (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xVertical)) - epsilon) - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xVertical)) ≤ mu.real (E.verticalCrossingEvent a b c d)) ∨ (1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ left x + epsilon ∧ left x * (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xHorizontal)) - epsilon) - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xHorizontal)) ≤ mu.real (E.horizontalCrossingEvent a b c d))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_approxPreferredSide_crossing_branch E mu hFKG a b c d hn hm epsilon hepsilon source bottom top left right hsource hbottomScore htopScore hleftScore hrightScore hbottom htop hleft hright

/--
[PeriodicPlaneEmbedding.exists_intrinsicEndpointError_crossing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma exists_intrinsicEndpointError_crossing_branch_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {n m : Nat}
  {source : PreferenceGridVertex n m → Finset V}
  {bottom top left right : PreferenceGridVertex n m → Real}
-- given
  (hFKG : IsFKG mu)
  (hn : 0 < n)
  (hm : 0 < m)
  (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a b c d)
  (hbottomScore : ∀ x, bottom x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectBottomBoundaryVertices a b c d)))
  (htopScore : ∀ x, top x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectTopBoundaryVertices a b c d)))
  (hleftScore : ∀ x, left x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectLeftBoundaryVertices a b c d)))
  (hrightScore : ∀ x, right x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectRightBoundaryVertices a b c d))) :
-- imply
  let epsilon := rectangleEndpointPreferenceError bottom top left right ∃ x xVertical xHorizontal : PreferenceGridVertex n m, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧ ((1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ bottom x + epsilon ∧ bottom x * (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xVertical)) - epsilon) - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xVertical)) ≤ mu.real (E.verticalCrossingEvent a b c d)) ∨ (1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ left x + epsilon ∧ left x * (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xHorizontal)) - epsilon) - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xHorizontal)) ≤ mu.real (E.horizontalCrossingEvent a b c d))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_intrinsicEndpointError_crossing_branch E mu hFKG a b c d hn hm source bottom top left right hsource hbottomScore htopScore hleftScore hrightScore

/--
[crossing_max_tendsto_one_of_approxPreferredSide_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma crossing_max_tendsto_one_of_approxPreferredSide_branches_eq
  [DecidableEq V]
  [Countable V]
  {A Hv Hh Mv Mh epsilon Cv Ch : Nat → Real}
-- given
  (hA : Tendsto A atTop (nhds 1))
  (hHv : Tendsto Hv atTop (nhds 1))
  (hHh : Tendsto Hh atTop (nhds 1))
  (hMv : Tendsto Mv atTop (nhds 0))
  (hMh : Tendsto Mh atTop (nhds 0))
  (hepsilon : Tendsto epsilon atTop (nhds 0))
  (hbranch : ∀ N, A N * (Hv N * A N - Mv N - epsilon N) - Mv N ≤ Cv N ∨ A N * (Hh N * A N - Mh N - epsilon N) - Mh N ≤ Ch N)
  (hCv : ∀ N, Cv N ≤ 1)
  (hCh : ∀ N, Ch N ≤ 1) :
-- imply
  Tendsto (fun N => max (Cv N) (Ch N)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.crossing_max_tendsto_one_of_approxPreferredSide_branches A Hv Hh Mv Mh epsilon Cv Ch hA hHv hHh hMv hMh hepsilon hbranch hCv hCh

/--
[crossing_selected_tendsto_one_of_approxPreferredSide_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma crossing_selected_tendsto_one_of_approxPreferredSide_branches_eq
  [DecidableEq V]
  [Countable V]
-- given
  (branch : Nat -> Bool)
  (A Hv Hh Mv Mh epsilon Cv Ch : Nat -> Real)
  (hA : Tendsto A atTop (nhds 1))
  (hHv : Tendsto Hv atTop (nhds 1))
  (hHh : Tendsto Hh atTop (nhds 1))
  (hMv : Tendsto Mv atTop (nhds 0))
  (hMh : Tendsto Mh atTop (nhds 0))
  (hepsilon : Tendsto epsilon atTop (nhds 0))
  (hvertical : forall N, branch N = true -> A N * (Hv N * A N - Mv N - epsilon N) - Mv N <= Cv N)
  (hhorizontal : forall N, branch N = false -> A N * (Hh N * A N - Mh N - epsilon N) - Mh N <= Ch N)
  (hCv : forall N, Cv N <= 1)
  (hCh : forall N, Ch N <= 1) :
-- imply
  Tendsto (fun N => if branch N then Cv N else Ch N) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.crossing_selected_tendsto_one_of_approxPreferredSide_branches branch A Hv Hh Mv Mh epsilon Cv Ch hA hHv hHh hMv hMh hepsilon hvertical hhorizontal hCv hCh

/--
[crossing_max_tendsto_one_of_approxPreferredSide_root_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma crossing_max_tendsto_one_of_approxPreferredSide_root_branches_eq
  [DecidableEq V]
  [Countable V]
  {root A Hv Hh Mv Mh epsilon Cv Ch : Nat → Real}
-- given
  (hroot : Tendsto root atTop (nhds 1))
  (hrootA : ∀ N, root N ≤ A N + epsilon N)
  (hAupper : ∀ N, A N ≤ 1)
  (hHv : Tendsto Hv atTop (nhds 1))
  (hHh : Tendsto Hh atTop (nhds 1))
  (hMv : Tendsto Mv atTop (nhds 0))
  (hMh : Tendsto Mh atTop (nhds 0))
  (hepsilon : Tendsto epsilon atTop (nhds 0))
  (hbranch : ∀ N, A N * (Hv N * A N - Mv N - epsilon N) - Mv N ≤ Cv N ∨ A N * (Hh N * A N - Mh N - epsilon N) - Mh N ≤ Ch N)
  (hCv : ∀ N, Cv N ≤ 1)
  (hCh : ∀ N, Ch N ≤ 1) :
-- imply
  Tendsto (fun N => max (Cv N) (Ch N)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.crossing_max_tendsto_one_of_approxPreferredSide_root_branches root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper hHv hHh hMv hMh hepsilon hbranch hCv hCh

/--
[crossing_selected_tendsto_one_of_approxPreferredSide_root_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean)
-/
@[path]
private lemma crossing_selected_tendsto_one_of_approxPreferredSide_root_branches_eq
  [DecidableEq V]
  [Countable V]
-- given
  (branch : Nat -> Bool)
  (root A Hv Hh Mv Mh epsilon Cv Ch : Nat -> Real)
  (hroot : Tendsto root atTop (nhds 1))
  (hrootA : forall N, root N <= A N + epsilon N)
  (hAupper : forall N, A N <= 1)
  (hHv : Tendsto Hv atTop (nhds 1))
  (hHh : Tendsto Hh atTop (nhds 1))
  (hMv : Tendsto Mv atTop (nhds 0))
  (hMh : Tendsto Mh atTop (nhds 0))
  (hepsilon : Tendsto epsilon atTop (nhds 0))
  (hvertical : forall N, branch N = true -> A N * (Hv N * A N - Mv N - epsilon N) - Mv N <= Cv N)
  (hhorizontal : forall N, branch N = false -> A N * (Hh N * A N - Mh N - epsilon N) - Mh N <= Ch N)
  (hCv : forall N, Cv N <= 1)
  (hCh : forall N, Ch N <= 1) :
-- imply
  Tendsto (fun N => if branch N then Cv N else Ch N) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.crossing_selected_tendsto_one_of_approxPreferredSide_root_branches branch root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper hHv hHh hMv hMh hepsilon hvertical hhorizontal hCv hCh


-- created on 2026-10-23
