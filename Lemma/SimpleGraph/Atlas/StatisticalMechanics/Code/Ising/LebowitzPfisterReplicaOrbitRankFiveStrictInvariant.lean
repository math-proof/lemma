import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
open StatMech StatMech.Ising


/--
[lpReplicaStrictPhysicalDoubleIncidenceRaw_map_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaStrictPhysicalDoubleIncidenceRaw_map_equiv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {E : Copy (lpReplicaCurrentGraph G sites) m ≃ Copy (lpReplicaCurrentGraph G sites) n}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (hends : ∀ c, endsM (lpReplicaCurrentGraph G sites) n (E c) = endsM (lpReplicaCurrentGraph G sites) m c)
  (hstrict : LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m K) :
-- imply
  LPReplicaStrictPhysicalDoubleIncidenceRaw G sites n (K.map E.toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplicaStrictPhysicalDoubleIncidenceRaw_map_equiv G sites E hends K hstrict

/--
[lpReplicaDecoratedOrbitAtomEquivOrientedFourColor_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomEquivOrientedFourColor_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {z : LPReplicaDecoratedOrbitAtom G sites A B q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A B q z).1.1 = z.1.1.1 := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomEquivOrientedFourColor_profile G sites A B q z

/--
[lpReplicaDecoratedOrbitAtomOfRowGate_hasStrictPhysicalDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRowGate_hasStrictPhysicalDoubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L) ↔ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m (lpReplicaRowCopies G sites m tag true) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRowGate_hasStrictPhysicalDoubleIncidence G sites m q tag A B hm hgate L

/--
[lpReplicaDecoratedOrbitAtomOfBalancedSelector_hasStrictPhysicalDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfBalancedSelector_hasStrictPhysicalDoubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T : Finset (LPReplicaCurrentVertex V)}
  {s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence G sites Si ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomOfBalancedSelector G sites Si Sj T q s) ↔ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites s.profile (lpReplicaRowCopies G sites s.profile (lpReplicaToggleRows G sites s.profile s.selector s.tag) true) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfBalancedSelector_hasStrictPhysicalDoubleIncidence G sites Si Sj T q s

/--
[lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaBalancedSelector G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left G sites i j q s) ↔ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites s.profile (lpReplicaRowCopies G sites s.profile (lpReplicaToggleRows G sites s.profile s.selector s.tag) true) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence G sites i j q s

/--
[lpReplica_not_strictPhysicalDoubleIncidence_insert_diagonal_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplica_not_strictPhysicalDoubleIncidence_insert_diagonal_matching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcdiag : (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag)
  (hunique : ∀ x ∈ K.biUnion (fun e => (endsM (lpReplicaCurrentGraph G sites) m e).toFinset), ∃! e, e ∈ K ∧ x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset) :
-- imply
  ¬ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m (insert c K) := by
-- proof
  apply StatMech.Ising.lpReplica_not_strictPhysicalDoubleIncidence_insert_diagonal_matching G sites m K c hcdiag hunique

/--
[lpReplica_not_strictPhysicalDoubleIncidence_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplica_not_strictPhysicalDoubleIncidence_matching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hunique : ∀ x ∈ K.biUnion (fun e => (endsM (lpReplicaCurrentGraph G sites) m e).toFinset), ∃! e, e ∈ K ∧ x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset) :
-- imply
  ¬ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m K := by
-- proof
  apply StatMech.Ising.lpReplica_not_strictPhysicalDoubleIncidence_matching G sites m K hunique

/--
[lpReplica_strictPhysicalDoubleIncidence_insert_parallel_pair_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplica_strictPhysicalDoubleIncidence_insert_parallel_pair_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c e : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hce : c ≠ e)
  (hcK : c ∉ K)
  (heK : e ∉ K)
  (hparallel : c.1.1 = e.1.1)
  (hunique : ∀ x ∈ K.biUnion (fun f => (endsM (lpReplicaCurrentGraph G sites) m f).toFinset), ∃! f, f ∈ K ∧ x ∈ (endsM (lpReplicaCurrentGraph G sites) m f).toFinset) :
-- imply
  LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m (insert c (insert e K)) ↔ ¬ (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag := by
-- proof
  apply StatMech.Ising.lpReplica_strictPhysicalDoubleIncidence_insert_parallel_pair_iff G sites m K c e hce hcK heK hparallel hunique

/--
[lpReplicaOffdiagDecoratedSource_rankFive_activeCore_uniqueIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rankFive_activeCore_uniqueIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false let E := endsM (lpReplicaCurrentGraph G sites) z.1.1.1 ∀ x ∈ K.biUnion (fun e => (E e).toFinset), ∃! e, e ∈ K ∧ x ∈ (E e).toFinset := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rankFive_activeCore_uniqueIncidence G sites hsite hij q z hthree

/--
[lpReplicaOffdiagDecoratedSource_rankFive_exists_parallelComplementPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rankFive_exists_parallelComplementPair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false ∃ c e, c ≠ e ∧ Finset.univ \ K = {c, e} ∧ c.1.1 = e.1.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rankFive_exists_parallelComplementPair G sites hsite hij q hcard z hthree

/--
[lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_singletonToggle_raw_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_singletonToggle_raw_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {a : Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (d.1 r).1 = true)
  (haK : a ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false ∃ c e, c ≠ e ∧ Finset.univ \ K = {c, e} ∧ (LPReplicaStrictPhysicalDoubleIncidenceRaw G sites z.1.1.1 (lpReplicaRowCopies G sites z.1.1.1 (lpReplicaToggleRows G sites z.1.1.1 {a} d.1) true) ↔ ¬ (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_singletonToggle_raw_iff G sites hsite hij q hcard z hhigh a haK

/--
[lpReplicaOffdiagDecoratedSource_rankFive_low_singletonToggle_not_strictRaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rankFive_low_singletonToggle_not_strictRaw_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {a : Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hlow : let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (d.1 r).1 = false)
  (haK : a ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z ¬ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites z.1.1.1 (lpReplicaRowCopies G sites z.1.1.1 (lpReplicaToggleRows G sites z.1.1.1 {a} d.1) true) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rankFive_low_singletonToggle_not_strictRaw G sites hsite hij q hcard z hlow a haK

/--
[lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom_hasDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom_hasDoubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j k u v : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (hu : u = i ∨ u = j ∨ u = k)
  (hv : v = i ∨ v = j ∨ v = k)
  (huv : u ≠ v)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites k)
  (hdK : d ∈ Finset.univ \ {c})
  (hfold : lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v)))
  (hunique : ∀ x ∈ lpReplicaTripleSeamGhostSource sites i j k, ∃! e, e ∈ Finset.univ \ {c} ∧ x ∈ (endsM (lpReplicaCurrentGraph G sites) z.1.1.1 e).toFinset)
  (hdisc : let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 (Finset.univ \ {d})) (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d}) let K' := lpReplicaPartialReflectCopiesRaw G sites z.1.1.1 {d} (Finset.univ \ {c}) ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K' lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) (lpReplicaThirdOfThree i j k u v) ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q (lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom G sites hsite hij hik hjk hu hv huv q z c d hc (Ne.symm ((Finset.mem_sdiff.mp hdK).2 ∘ Finset.mem_singleton.mpr)) hfold hdisc) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom_hasDoubleIncidence G sites hsite hij hik hjk hu hv huv q z c d hc hdK hfold hunique hdisc


-- created on 2026-10-23
