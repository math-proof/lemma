/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part5
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_step3SourceEvent (T : MonotoneAutomaton d)
    (D N : ℕ) (i : (Finset (Site d) × Site d) × Site d) :
    MeasurableSet (step3SourceEvent T D N i) := by
  let M := i.1.1
  let x := i.1.2
  let y := i.2
  by_cases hsub : (↑(contactForceSet x y) : Set (Site d)) ⊆ ↑M
  · by_cases hdist : l1dist d x y = D
    · have hmask := measurableSet_step3MaskMatches T D N M
      have hlow := (measurable_zeroHighPair T M)
        (measurableSet_pairLowInfinite x)
      have hhigh := (measurable_zeroHighPair T M)
        (measurableSet_pairHighConnected 0 y)
      have hdisjoint := (measurable_zeroHighPair T (contactForceSet x y))
        (measurableSet_pairDisjointInfiniteHighAt 0)
      have heq := measurableSet_pairHighCluster_eq_preimage
        (zeroHighPair T (contactForceSet x y)) (zeroHighPair T M)
        (measurable_zeroHighPair T (contactForceSet x y))
        (measurable_zeroHighPair T M) 0
      simpa only [step3SourceEvent, M, x, y, hsub, hdist, true_and] using
        hmask.inter (hlow.inter (hhigh.inter (hdisjoint.inter heq)))
    · have hempty : step3SourceEvent T D N i = ∅ := by
        ext q
        simp [step3SourceEvent, x, y, hdist]
      rw [hempty]
      exact MeasurableSet.empty
  · have hempty : step3SourceEvent T D N i = ∅ := by
      ext q
      simp [step3SourceEvent, M, x, y, hsub]
    rw [hempty]
    exact MeasurableSet.empty

theorem measurableSet_step3TargetEvent (T : MonotoneAutomaton d)
    (D N : ℕ) (i : (Finset (Site d) × Site d) × Site d) :
    MeasurableSet (step3TargetEvent T D N i) :=
  (measurableSet_step3SourceEvent T D N i).inter
    (measurableSet_highThresholdOn T.threshold (contactForceSet i.1.2 i.2))

theorem zeroFields_eq_of_eq_off (S : Finset (Site d))
    {xi xi' : NonnegativeField d}
    (h : ∀ z ∉ S, xi z = xi' z) : zeroFields xi S = zeroFields xi' S := by
  funext z
  by_cases hz : z ∈ S
  · simp [zeroFields, hz]
  · simp [zeroFields, hz, h z hz]

theorem zeroHighPair_eq_of_eq_off (T : MonotoneAutomaton d)
    (S : Finset (Site d)) {q q' : FieldTriple d}
    (hlow : q.1 = q'.1) (hmiddle : q.2.1 = q'.2.1)
    (hhigh : ∀ z ∉ S, q.2.2 z = q'.2.2 z) :
    zeroHighPair T S q = zeroHighPair T S q' := by
  unfold zeroHighPair
  congr 1
  · unfold interpolatedSite
    funext z
    rw [hlow, hmiddle]
  · rw [zeroFields_eq_of_eq_off S hhigh]


theorem step3SourceEvent_ignoresHigh (T : MonotoneAutomaton d) (D N : ℕ)
    (i : (Finset (Site d) × Site d) × Site d) :
    TripleEventIgnoresHighOn (contactForceSet i.1.2 i.2)
      (step3SourceEvent T D N i) := by
  intro q q' hlow hmiddle hhigh
  by_cases hsub : (↑(contactForceSet i.1.2 i.2) : Set (Site d)) ⊆ ↑i.1.1
  · have hforce : zeroHighPair T (contactForceSet i.1.2 i.2) q =
        zeroHighPair T (contactForceSet i.1.2 i.2) q' :=
      zeroHighPair_eq_of_eq_off T _ hlow hmiddle hhigh
    have hMoff : ∀ z ∉ i.1.1, q.2.2 z = q'.2.2 z := by
      intro z hzM
      apply hhigh z
      exact fun hzF => hzM (hsub hzF)
    have hbase : zeroHighPair T i.1.1 q = zeroHighPair T i.1.1 q' :=
      zeroHighPair_eq_of_eq_off T i.1.1 hlow hmiddle hMoff
    have hmask : step3MaskMatches T D N i.1.1 q ↔
        step3MaskMatches T D N i.1.1 q' := by
      unfold step3MaskMatches
      rw [hbase]
    simp only [step3SourceEvent, Set.mem_setOf_eq]
    rw [hforce, hbase]
    exact and_congr hmask Iff.rfl
  · have hq : q ∉ step3SourceEvent T D N i := by
      simp [step3SourceEvent, hsub]
    have hq' : q' ∉ step3SourceEvent T D N i := by
      simp [step3SourceEvent, hsub]
    exact iff_of_false hq hq'

@[simp] theorem pairLowInfiniteVertices_zeroHighPair
    (T : MonotoneAutomaton d) (S : Finset (Site d)) (q : FieldTriple d) :
    pairLowInfiniteVertices (zeroHighPair T S q) =
      pairLowInfiniteVertices (interpolatedHighPair T q) := rfl

theorem pairHighCluster_zeroHighPair_eq_siteCluster
    (T : MonotoneAutomaton d) (S : Finset (Site d))
    (q : FieldTriple d) (x : Site d) :
    pairHighCluster (zeroHighPair T S q) x =
      siteCluster (T (zeroFields q.2.2 S)) x := by
  ext z
  exact connected_siteToBond_iff _ _ _

theorem site_eq_true_of_pairHighCluster_infinite
    (omega : PairSiteConfig d) (x : Site d)
    (hinf : (pairHighCluster omega x).Infinite) :
    pairSiteRight omega x = true := by
  apply site_eq_true_of_siteCluster_infinite
  have heq : siteCluster (pairSiteRight omega) x =
      pairHighCluster omega x := by
    ext z
    exact (connected_siteToBond_iff (pairSiteRight omega) x z).symm
  rw [heq]
  exact hinf


theorem step3TargetEvent_forceSets_inter_nonempty
    (T : MonotoneAutomaton d) (D N : ℕ) (q : FieldTriple d)
    {i j : (Finset (Site d) × Site d) × Site d}
    (hi : q ∈ step3TargetEvent T D N i)
    (hj : q ∈ step3TargetEvent T D N j) :
    (contactForceSet i.1.2 i.2 ∩ contactForceSet j.1.2 j.2).Nonempty := by
  classical
  rcases hi with ⟨hiSource, hiThreshold⟩
  rcases hj with ⟨hjSource, hjThreshold⟩
  rcases hiSource with
    ⟨hiMask, hiSub, hiDist, hix, hiy, hiDisjoint, hiClusterEq⟩
  rcases hjSource with
    ⟨hjMask, hjSub, hjDist, hjx, hjy, hjDisjoint, hjClusterEq⟩
  by_contra hinter
  have hdisj : Disjoint (contactForceSet i.1.2 i.2)
      (contactForceSet j.1.2 j.2) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.not_nonempty_iff_eq_empty.mp hinter
  have hmaskEq : i.1.1 = j.1.1 := by
    ext z
    rw [hiMask z, hjMask z]
    simp only [pairLowInfiniteVertices_zeroHighPair]
  have hjy' : j.2 ∈
      pairHighCluster (zeroHighPair T (contactForceSet i.1.2 i.2) q) 0 := by
    rw [hiClusterEq, hmaskEq]
    exact hjy
  have hinfI : (pairHighCluster
      (zeroHighPair T (contactForceSet i.1.2 i.2) q) 0).Infinite :=
    hiDisjoint.1
  have hyCluster : pairHighCluster
      (zeroHighPair T (contactForceSet i.1.2 i.2) q) j.2 =
      pairHighCluster
        (zeroHighPair T (contactForceSet i.1.2 i.2) q) 0 :=
    pairHighCluster_eq_of_mem hjy'
  have hyOpen : T (zeroFields q.2.2 (contactForceSet i.1.2 i.2)) j.2 = true := by
    change pairSiteRight
      (zeroHighPair T (contactForceSet i.1.2 i.2) q) j.2 = true
    apply site_eq_true_of_pairHighCluster_infinite
    rw [hyCluster]
    exact hinfI
  have hforceOpen : ∀ z ∈ contactForceSet j.1.2 j.2,
      T (zeroFields q.2.2 (contactForceSet i.1.2 i.2)) z = true := by
    intro z hzj
    apply T.occupationThreshold
    have hzi : z ∉ contactForceSet i.1.2 i.2 := by
      exact fun hzi => Finset.disjoint_left.mp hdisj hzi hzj
    simpa [zeroFields, hzi] using hjThreshold z hzj
  have hconn : Connected d
      (siteToBond (T (zeroFields q.2.2 (contactForceSet i.1.2 i.2))))
      j.1.2 j.2 :=
    connected_siteToBond_of_contactForceSet _ _ _ hyOpen hforceOpen
  have hxHigh : j.1.2 ∈
      pairHighCluster (zeroHighPair T (contactForceSet i.1.2 i.2) q) 0 := by
    exact hjy'.trans hconn.symm
  have hxLow : j.1.2 ∈ pairLowInfiniteVertices
      (zeroHighPair T (contactForceSet i.1.2 i.2) q) := by
    simpa only [pairLowInfiniteVertices_zeroHighPair] using hjx
  exact hiDisjoint.2 ⟨j.1.2, hxHigh, hxLow⟩


end StatMech.FrontierA
