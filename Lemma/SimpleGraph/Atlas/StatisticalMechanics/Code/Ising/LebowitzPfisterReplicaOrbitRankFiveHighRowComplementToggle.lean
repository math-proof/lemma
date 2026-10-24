import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle
open Finset StatMech StatMech.Ising


/--
[lpReplicaToggleRows_swapRowsTag_eq_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaToggleRows_swapRowsTag_eq_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaToggleRows G sites m P (lpReplicaSwapRowsTag tag) = lpReplicaToggleRows G sites m (Finset.univ \ P) tag := by
-- proof
  apply StatMech.Ising.lpReplicaToggleRows_swapRowsTag_eq_compl G sites m P tag

/--
[lpReplicaToggleRows_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaToggleRows_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaToggleRows G sites m P (lpReplicaToggleRows G sites m P tag) = tag := by
-- proof
  apply StatMech.Ising.lpReplicaToggleRows_self G sites m P tag

/--
[lpReplicaToggleRows_activeSdiff_swapRowsTag_eq_singleton_after_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaToggleRows_activeSdiff_swapRowsTag_eq_singleton_after_complement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcK : c ∈ K)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaToggleRows G sites m (K \ {c}) (lpReplicaSwapRowsTag tag) = lpReplicaToggleRows G sites m {c} (lpReplicaToggleRows G sites m (Finset.univ \ K) tag) := by
-- proof
  apply StatMech.Ising.lpReplicaToggleRows_activeSdiff_swapRowsTag_eq_singleton_after_complement G sites m K c hcK tag

/--
[lpReplicaToggleRows_activeSdiff_swapRowsComplementTag_eq_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaToggleRows_activeSdiff_swapRowsComplementTag_eq_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcK : c ∈ K)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaToggleRows G sites m (K \ {c}) (lpReplicaSwapRowsTag (lpReplicaToggleRows G sites m (Finset.univ \ K) tag)) = lpReplicaToggleRows G sites m {c} tag := by
-- proof
  apply StatMech.Ising.lpReplicaToggleRows_activeSdiff_swapRowsComplementTag_eq_singleton G sites m K c hcK tag

/--
[lpReplicaToggleRows_singleton_after_complement_ne_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaToggleRows_singleton_after_complement_ne_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcK : c ∈ K)
  (hC : (Finset.univ \ K).Nonempty)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaToggleRows G sites m {c} (lpReplicaToggleRows G sites m (Finset.univ \ K) tag) ≠ lpReplicaToggleRows G sites m {c} tag := by
-- proof
  apply StatMech.Ising.lpReplicaToggleRows_singleton_after_complement_ne_singleton G sites m K c hcK hC tag

/--
[lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_iSeam_complementTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_iSeam_complementTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (d.1 r).1 = true)
  (hcK : c ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
-- imply
  ∃ s : LPReplicaBalancedSelector G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧ HEq s.selector (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false \ {c}) ∧ @HEq (Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) s.profile)) (lpReplicaRowCopies G sites s.profile (lpReplicaToggleRows G sites s.profile s.selector s.tag) true) (Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1)) (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false \ {c}) ∧ ∃ y : LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧ ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q (Sum.inl y) ∧ y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left G sites i j q s := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_iSeam_complementTarget G sites hsite hij q hcard z hhigh c hcK hc

/--
[lpReplicaOffdiagDecoratedTargetToAggregate_hasStrictPhysicalDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedTargetToAggregate_hasStrictPhysicalDoubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y) ↔ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q y := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedTargetToAggregate_hasStrictPhysicalDoubleIncidence G sites i j q y

/--
[lpReplicaOffdiagDecoratedTargetToAggregate_ne_strictRouteCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedTargetToAggregate_ne_strictRouteCandidate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hy : ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q y) :
-- imply
  lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y ≠ lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedTargetToAggregate_ne_strictRouteCandidate G sites hsite q hcard y hy z d

/--
[lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y y.1 = y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_self G sites q y

/--
[lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_flip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y).1 = lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_flip G sites q y

/--
[lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_not_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_not_strict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
  {b : Fin 2}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hy : ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q y) :
-- imply
  ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q (lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y b) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_not_strict G sites q y hy b

/--
[lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_strictRouteCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_strictRouteCandidate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
  {b : Fin 2}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hy : ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q y) :
-- imply
  lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y b ≠ lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_strictRouteCandidate G sites hsite q hcard y hy b z d

/--
[lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
  {b : Fin 2}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y b).2 = y.2 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key G sites q y b

/--
[lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key_eq_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key_eq_of_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y w : LPReplicaAggregateDecoratedTarget G sites q}
  {b c : Fin 2}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y b = lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q w c) :
-- imply
  y.2 = w.2 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key_eq_of_eq G sites q y w b c h

/--
[lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_of_key_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_of_key_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y w : LPReplicaAggregateDecoratedTarget G sites q}
  {b c : Fin 2}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hkey : y.2 ≠ w.2) :
-- imply
  lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y b ≠ lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q w c := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_of_key_ne G sites q y w hkey b c

/--
[lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode_not_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode_not_strict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s : S}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (bit : S -> Fin 2)
  (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
  (hcode : Function.Injective (fun s => (bit s, key s)))
  (hnonstrict : ∀ s, ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q ⟨0, key s⟩) :
-- imply
  ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q (lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode G sites q bit key hcode s) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode_not_strict G sites q bit key hcode hnonstrict s

/--
[nonempty_lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma nonempty_lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Nonempty (LPReplicaAggregateRankFiveSupportedStrictRouteEmbedding G sites hsite q hcard) := by
-- proof
  apply StatMech.Ising.nonempty_lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding G sites hsite q hcard

/--
[lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding_strict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q ((lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding G sites hsite q hcard).toEmbedding z) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding_strict G sites hsite q hcard z

/--
[lpReplicaOffdiagRankFiveOutputCollisionClass_card_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaOffdiagRankFiveOutputCollisionClass_card_le_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (output : LPReplicaOffdiagDecoratedSource G sites i j q -> LPReplicaOffdiagDecoratedTarget G sites i j q) :
-- imply
  (lpReplicaOffdiagRankFiveOutputCollisionClass G sites i j q output y).card ≤ 4 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRankFiveOutputCollisionClass_card_le_four G sites hsite hij q hcard output y

/--
[lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_le_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (output : LPReplicaOffdiagDecoratedSource G sites i j q -> LPReplicaOffdiagDecoratedTarget G sites i j q) :
-- imply
  (lpReplicaOffdiagRankFiveOutputCollisionClassLow G sites i j q output y).card ≤ 3 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_le_three G sites hsite hij q hcard output y

/--
[lpReplicaOffdiagRankFiveOutputCollisionClassHigh_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaOffdiagRankFiveOutputCollisionClassHigh_card_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (output : LPReplicaOffdiagDecoratedSource G sites i j q -> LPReplicaOffdiagDecoratedTarget G sites i j q) :
-- imply
  (lpReplicaOffdiagRankFiveOutputCollisionClassHigh G sites i j q output y).card ≤ 1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRankFiveOutputCollisionClassHigh_card_le_one G sites hsite hij q hcard output y

/--
[lpReplicaOffdiagRankFiveOutputCollisionClass_eq_low_union_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaOffdiagRankFiveOutputCollisionClass_eq_low_union_high_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (output : LPReplicaOffdiagDecoratedSource G sites i j q -> LPReplicaOffdiagDecoratedTarget G sites i j q) :
-- imply
  by classical exact lpReplicaOffdiagRankFiveOutputCollisionClass G sites i j q output y = (lpReplicaOffdiagRankFiveOutputCollisionClassLow G sites i j q output y) ∪ (lpReplicaOffdiagRankFiveOutputCollisionClassHigh G sites i j q output y) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRankFiveOutputCollisionClass_eq_low_union_high G sites hsite hij q hcard output y

/--
[lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_ge_two_of_three_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean)
-/
@[path]
private lemma lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_ge_two_of_three_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (output : LPReplicaOffdiagDecoratedSource G sites i j q -> LPReplicaOffdiagDecoratedTarget G sites i j q)
  (hthree : 3 ≤ (lpReplicaOffdiagRankFiveOutputCollisionClass G sites i j q output y).card) :
-- imply
  2 ≤ (lpReplicaOffdiagRankFiveOutputCollisionClassLow G sites i j q output y).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_ge_two_of_three_le G sites hsite hij q hcard output y hthree


-- created on 2026-10-23
