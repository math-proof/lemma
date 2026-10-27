import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part12
open MeasureTheory Set Finset SimpleGraph StatMech StatMech.FrontierA


/--
[siteCluster_raiseFields_eq_of_final_infinite_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma siteCluster_raiseFields_eq_of_final_infinite_of_avoids_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {xi : NonnegativeField d}
  {S : Finset (Site d)}
  {y : Site d}
-- given
  (r : Site d → ℝ≥0)
  (hinf : (siteCluster (T (raiseFields xi S r)) y).Infinite)
  (havoid : ∀ x ∈ S, x ∉ siteCluster (T (raiseFields xi S r)) y) :
-- imply
  siteCluster (T (raiseFields xi S r)) y = siteCluster (T xi) y := by
-- proof
  apply StatMech.FrontierA.siteCluster_raiseFields_eq_of_final_infinite_of_avoids T xi S r y hinf havoid

/--
[siteCluster_zeroFields_eq_of_final_infinite_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma siteCluster_zeroFields_eq_of_final_infinite_of_avoids_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {xi : NonnegativeField d}
  {S : Finset (Site d)}
  {y : Site d}
-- given
  (hinf : (siteCluster (T xi) y).Infinite)
  (havoid : ∀ x ∈ S, x ∉ siteCluster (T xi) y) :
-- imply
  siteCluster (T (zeroFields xi S)) y = siteCluster (T xi) y := by
-- proof
  apply StatMech.FrontierA.siteCluster_zeroFields_eq_of_final_infinite_of_avoids T xi S y hinf havoid

/--
[left_mem_coordinateBetween](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma left_mem_coordinateBetween_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  x ∈ coordinateBetween x y := by
-- proof
  apply StatMech.FrontierA.left_mem_coordinateBetween x y

/--
[right_mem_coordinateBetween](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma right_mem_coordinateBetween_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  y ∈ coordinateBetween x y := by
-- proof
  apply StatMech.FrontierA.right_mem_coordinateBetween x y

/--
[coordinateBetween_l1dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma coordinateBetween_l1dist_le_eq
  {d : ℕ}
  {x y z : Site d}
-- given
  (hz : z ∈ coordinateBetween x y) :
-- imply
  l1dist d x z ≤ l1dist d x y := by
-- proof
  apply StatMech.FrontierA.coordinateBetween_l1dist_le hz

/--
[eq_right_of_mem_coordinateBetween_of_l1dist_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma eq_right_of_mem_coordinateBetween_of_l1dist_eq_eq
  {d : ℕ}
  {x y z : Site d}
-- given
  (hz : z ∈ coordinateBetween x y)
  (heq : l1dist d x z = l1dist d x y) :
-- imply
  z = y := by
-- proof
  apply StatMech.FrontierA.eq_right_of_mem_coordinateBetween_of_l1dist_eq hz heq

/--
[coordinateBetween_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma coordinateBetween_finite_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  (coordinateBetween x y).Finite := by
-- proof
  apply StatMech.FrontierA.coordinateBetween_finite x y

/--
[mixSite_mem_coordinateBetween](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma mixSite_mem_coordinateBetween_eq
  {d : ℕ}
  {x y : Site d}
  {k : ℕ} :
-- imply
  mixSite x y k ∈ coordinateBetween x y := by
-- proof
  apply StatMech.FrontierA.mixSite_mem_coordinateBetween x y k

/--
[coordinateBetween_update_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma coordinateBetween_update_reachable_eq
  {d : ℕ}
  {x y u : Site d}
  {j : Fin d}
-- given
  (hu : u ∈ coordinateBetween x y) :
-- imply
  ((hypercubicLattice d).induce (coordinateBetween x y)).Reachable ⟨u, hu⟩ ⟨Function.update u j (y j), by intro i by_cases hij : i = j · subst i simp · simpa [Function.update_of_ne hij] using hu i⟩ := by
-- proof
  apply StatMech.FrontierA.coordinateBetween_update_reachable x y u hu j

/--
[coordinateBetween_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma coordinateBetween_reachable_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  ((hypercubicLattice d).induce (coordinateBetween x y)).Reachable ⟨x, left_mem_coordinateBetween x y⟩ ⟨y, right_mem_coordinateBetween x y⟩ := by
-- proof
  apply StatMech.FrontierA.coordinateBetween_reachable x y

/--
[connected_siteToBond_of_coordinateBetween](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma connected_siteToBond_of_coordinateBetween_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d}
-- given
  (hopen : ∀ z ∈ coordinateBetween x y, eta z = true) :
-- imply
  Connected d (siteToBond eta) x y := by
-- proof
  apply StatMech.FrontierA.connected_siteToBond_of_coordinateBetween eta x y hopen

/--
[mem_contactForceSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma mem_contactForceSet_eq
  {d : ℕ}
  {x y z : Site d} :
-- imply
  z ∈ contactForceSet x y ↔ z ∈ coordinateBetween x y ∧ z ≠ y := by
-- proof
  apply StatMech.FrontierA.mem_contactForceSet

/--
[connected_siteToBond_of_contactForceSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma connected_siteToBond_of_contactForceSet_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d}
-- given
  (hy : eta y = true)
  (hforce : ∀ z ∈ contactForceSet x y, eta z = true) :
-- imply
  Connected d (siteToBond eta) x y := by
-- proof
  apply StatMech.FrontierA.connected_siteToBond_of_contactForceSet eta x y hy hforce

/--
[pairSiteLeft_zeroHighPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma pairSiteLeft_zeroHighPair_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {S : Finset (Site d)}
  {q : FieldTriple d} :
-- imply
  pairSiteLeft (zeroHighPair T S q) = interpolatedSite T q := by
-- proof
  apply StatMech.FrontierA.pairSiteLeft_zeroHighPair T S q

/--
[pairSiteRight_zeroHighPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma pairSiteRight_zeroHighPair_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {S : Finset (Site d)}
  {q : FieldTriple d} :
-- imply
  pairSiteRight (zeroHighPair T S q) = T (zeroFields q.2.2 S) := by
-- proof
  apply StatMech.FrontierA.pairSiteRight_zeroHighPair T S q

/--
[measurable_zeroFields](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurable_zeroFields_eq
  {d : ℕ}
  {S : Finset (Site d)} :
-- imply
  Measurable (fun xi : NonnegativeField d => zeroFields xi S) := by
-- proof
  apply StatMech.FrontierA.measurable_zeroFields S

/--
[measurable_zeroHighPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurable_zeroHighPair_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {S : Finset (Site d)} :
-- imply
  Measurable (zeroHighPair T S : FieldTriple d → PairSiteConfig d) := by
-- proof
  apply StatMech.FrontierA.measurable_zeroHighPair T S

/--
[measurableSet_pairHighCluster_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurableSet_pairHighCluster_eq_preimage_eq
  {d : ℕ}
  {f g : FieldTriple d → PairSiteConfig d}
  {root : Site d}
-- given
  (hf : Measurable f)
  (hg : Measurable g) :
-- imply
  MeasurableSet {q | pairHighCluster (f q) root = pairHighCluster (g q) root} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairHighCluster_eq_preimage f g hf hg root

/--
[measurableSet_step3MaskMatches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurableSet_step3MaskMatches_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {M : Finset (Site d)} :
-- imply
  MeasurableSet {q : FieldTriple d | step3MaskMatches T D N M q} := by
-- proof
  apply StatMech.FrontierA.measurableSet_step3MaskMatches T D N M

/--
[measurableSet_step3SourceEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurableSet_step3SourceEvent_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {i : (Finset (Site d) × Site d) × Site d} :
-- imply
  MeasurableSet (step3SourceEvent T D N i) := by
-- proof
  apply StatMech.FrontierA.measurableSet_step3SourceEvent T D N i

/--
[measurableSet_step3TargetEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurableSet_step3TargetEvent_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {i : (Finset (Site d) × Site d) × Site d} :
-- imply
  MeasurableSet (step3TargetEvent T D N i) := by
-- proof
  apply StatMech.FrontierA.measurableSet_step3TargetEvent T D N i

/--
[zeroFields_eq_of_eq_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma zeroFields_eq_of_eq_off_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {xi xi' : NonnegativeField d}
-- given
  (h : ∀ z ∉ S, xi z = xi' z) :
-- imply
  zeroFields xi S = zeroFields xi' S := by
-- proof
  apply StatMech.FrontierA.zeroFields_eq_of_eq_off S h

/--
[zeroHighPair_eq_of_eq_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma zeroHighPair_eq_of_eq_off_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {S : Finset (Site d)}
  {q q' : FieldTriple d}
-- given
  (hlow : q.1 = q'.1)
  (hmiddle : q.2.1 = q'.2.1)
  (hhigh : ∀ z ∉ S, q.2.2 z = q'.2.2 z) :
-- imply
  zeroHighPair T S q = zeroHighPair T S q' := by
-- proof
  apply StatMech.FrontierA.zeroHighPair_eq_of_eq_off T S hlow hmiddle hhigh

/--
[step3SourceEvent_ignoresHigh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3SourceEvent_ignoresHigh_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {i : (Finset (Site d) × Site d) × Site d} :
-- imply
  TripleEventIgnoresHighOn (contactForceSet i.1.2 i.2) (step3SourceEvent T D N i) := by
-- proof
  apply StatMech.FrontierA.step3SourceEvent_ignoresHigh T D N i

/--
[pairLowInfiniteVertices_zeroHighPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma pairLowInfiniteVertices_zeroHighPair_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {S : Finset (Site d)}
  {q : FieldTriple d} :
-- imply
  pairLowInfiniteVertices (zeroHighPair T S q) = pairLowInfiniteVertices (interpolatedHighPair T q) := by
-- proof
  apply StatMech.FrontierA.pairLowInfiniteVertices_zeroHighPair T S q

/--
[pairHighCluster_zeroHighPair_eq_siteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma pairHighCluster_zeroHighPair_eq_siteCluster_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {S : Finset (Site d)}
  {q : FieldTriple d}
  {x : Site d} :
-- imply
  pairHighCluster (zeroHighPair T S q) x = siteCluster (T (zeroFields q.2.2 S)) x := by
-- proof
  apply StatMech.FrontierA.pairHighCluster_zeroHighPair_eq_siteCluster T S q x

/--
[site_eq_true_of_pairHighCluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma site_eq_true_of_pairHighCluster_infinite_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x : Site d}
-- given
  (hinf : (pairHighCluster omega x).Infinite) :
-- imply
  pairSiteRight omega x = true := by
-- proof
  apply StatMech.FrontierA.site_eq_true_of_pairHighCluster_infinite omega x hinf

/--
[step3TargetEvent_forceSets_inter_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3TargetEvent_forceSets_inter_nonempty_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {q : FieldTriple d}
  {i j : (Finset (Site d) × Site d) × Site d}
-- given
  (hi : q ∈ step3TargetEvent T D N i)
  (hj : q ∈ step3TargetEvent T D N j) :
-- imply
  (contactForceSet i.1.2 i.2 ∩ contactForceSet j.1.2 j.2).Nonempty := by
-- proof
  apply StatMech.FrontierA.step3TargetEvent_forceSets_inter_nonempty T D N q hi hj

/--
[mem_shiftedBoxFinset_of_l1dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma mem_shiftedBoxFinset_of_l1dist_le_eq
  {d : ℕ}
  {z x : Site d}
  {D : ℕ}
-- given
  (h : l1dist d z x ≤ D) :
-- imply
  x ∈ shiftedBoxFinset z D := by
-- proof
  apply StatMech.FrontierA.mem_shiftedBoxFinset_of_l1dist_le h

/--
[shiftedBoxFinset_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma shiftedBoxFinset_card_le_eq
  {d : ℕ}
  {z : Site d}
  {D : ℕ} :
-- imply
  (shiftedBoxFinset z D).card ≤ (boxFinsetBK d D).card := by
-- proof
  apply StatMech.FrontierA.shiftedBoxFinset_card_le z D

/--
[contactForceSet_card_le_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma contactForceSet_card_le_box_eq
  {d : ℕ}
  {x y : Site d}
  {D : ℕ}
-- given
  (hxy : l1dist d x y = D) :
-- imply
  (contactForceSet x y).card ≤ (boxFinsetBK d D).card := by
-- proof
  apply StatMech.FrontierA.contactForceSet_card_le_box hxy

/--
[contactOverlapPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma contactOverlapPairs_card_le_eq
  {d : ℕ}
  {i : (Finset (Site d) × Site d) × Site d}
  {D : ℕ}
-- given
  (hiDist : l1dist d i.1.2 i.2 = D) :
-- imply
  (contactOverlapPairs i D).card ≤ (boxFinsetBK d D).card ^ 3 := by
-- proof
  apply StatMech.FrontierA.contactOverlapPairs_card_le i D hiDist

/--
[step3TargetMultiplicity_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3TargetMultiplicity_le_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {q : FieldTriple d} :
-- imply
  finiteEventMultiplicity (step3Indices (d := d) N) (step3TargetEvent T D N) q ≤ (boxFinsetBK d D).card ^ 3 := by
-- proof
  apply StatMech.FrontierA.step3TargetMultiplicity_le T D N q

/--
[highInsertionLowerBound_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma highInsertionLowerBound_le_one_eq
  {d : ℕ}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
  {t : NNReal}
-- given
  (epsilon : ℝ≥0∞)
  (hinsert : HasHighInsertionLowerBound mu t epsilon) :
-- imply
  epsilon ≤ 1 := by
-- proof
  apply StatMech.FrontierA.highInsertionLowerBound_le_one mu t epsilon hinsert

/--
[step3SourceTarget_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3SourceTarget_transfer_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
  {D N : ℕ}
  {i : (Finset (Site d) × Site d) × Site d}
-- given
  (epsilon : ℝ≥0∞)
  (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
-- imply
  epsilon ^ (boxFinsetBK d D).card * mu (step3SourceEvent T D N i) ≤ mu (step3TargetEvent T D N i) := by
-- proof
  apply StatMech.FrontierA.step3SourceTarget_transfer T mu D N epsilon hinsert i

/--
[measurable_finiteEventMultiplicity_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurable_finiteEventMultiplicity_countable_eq
  {d : ℕ}
  [MeasurableSpace Omega]
  [Countable I]
  {J : Finset I}
  {A : I → Set Omega}
-- given
  (hA : ∀ i ∈ J, MeasurableSet (A i)) :
-- imply
  Measurable (finiteEventMultiplicity J A) := by
-- proof
  apply StatMech.FrontierA.measurable_finiteEventMultiplicity_countable J A hA

/--
[measurableSet_step3SourceDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurableSet_step3SourceDegree_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N K : ℕ} :
-- imply
  MeasurableSet {q : FieldTriple d | K ≤ finiteEventMultiplicity (step3Indices (d := d) N) (step3SourceEvent T D N) q} := by
-- proof
  apply StatMech.FrontierA.measurableSet_step3SourceDegree T D N K

/--
[step3FiniteWindow_probability_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3FiniteWindow_probability_bound_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
  {D N K : ℕ}
  {E : Set (FieldTriple d)}
-- given
  (epsilon : ℝ≥0∞)
  (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon)
  (hEmeas : MeasurableSet E)
  (hdegree : ∀ q ∈ E, K ≤ finiteEventMultiplicity (step3Indices (d := d) N) (step3SourceEvent T D N) q) :
-- imply
  epsilon ^ (boxFinsetBK d D).card * K * mu E ≤ (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
-- proof
  apply StatMech.FrontierA.step3FiniteWindow_probability_bound T mu D N K epsilon hinsert E hEmeas hdegree

/--
[measurableSet_pairStep3DistanceAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurableSet_pairStep3DistanceAt_eq
  {d : ℕ}
  {root : Site d}
  {D : ℕ} :
-- imply
  MeasurableSet (pairStep3DistanceAt root D) := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairStep3DistanceAt root D

/--
[pairStep3CoreAt_eq_iUnion_distance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma pairStep3CoreAt_eq_iUnion_distance_eq
  {d : ℕ}
  {root : Site d} :
-- imply
  pairStep3CoreAt root = ⋃ D : ℕ, pairStep3DistanceAt root D := by
-- proof
  apply StatMech.FrontierA.pairStep3CoreAt_eq_iUnion_distance root

/--
[measurableSet_step3ContactEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurableSet_step3ContactEvent_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D : ℕ}
  {p : Site d × Site d} :
-- imply
  MeasurableSet (step3ContactEvent T D p) := by
-- proof
  apply StatMech.FrontierA.measurableSet_step3ContactEvent T D p

/--
[measurableSet_step3CoreWindowEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma measurableSet_step3CoreWindowEvent_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N K : ℕ} :
-- imply
  MeasurableSet (step3CoreWindowEvent T D N K) := by
-- proof
  apply StatMech.FrontierA.measurableSet_step3CoreWindowEvent T D N K

/--
[boxFinsetBK_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma boxFinsetBK_mono_eq
  {d : ℕ}
  {N M : ℕ}
-- given
  (hNM : N ≤ M) :
-- imply
  boxFinsetBK d N ⊆ boxFinsetBK d M := by
-- proof
  apply StatMech.FrontierA.boxFinsetBK_mono hNM

/--
[step3WindowContacts_card_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3WindowContacts_card_mono_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D : ℕ}
  {N M : ℕ}
  {q : FieldTriple d}
-- given
  (hNM : N ≤ M) :
-- imply
  (step3WindowContacts T D N q).card ≤ (step3WindowContacts T D M q).card := by
-- proof
  apply StatMech.FrontierA.step3WindowContacts_card_mono T D hNM q

/--
[step3CoreWindowEvent_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3CoreWindowEvent_mono_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D K : ℕ} :
-- imply
  Monotone (fun N => step3CoreWindowEvent T D N K) := by
-- proof
  apply StatMech.FrontierA.step3CoreWindowEvent_mono T D K

/--
[exists_low_contact_distance_of_mem_nearest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma exists_low_contact_distance_of_mem_nearest_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {root y : Site d}
  {D : ℕ}
-- given
  (hD : omega ∈ pairStep3DistanceAt root D)
  (hy : y ∈ pairNearestHighSet omega root) :
-- imply
  ∃ x ∈ pairLowInfiniteVertices omega, l1dist d x y = D := by
-- proof
  apply StatMech.FrontierA.exists_low_contact_distance_of_mem_nearest hD hy

/--
[step3Distance_preimage_eq_iUnion_windows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3Distance_preimage_eq_iUnion_windows_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D K : ℕ} :
-- imply
  (interpolatedHighPair T) ⁻¹' pairStep3DistanceAt (0 : Site d) D = ⋃ N : ℕ, step3CoreWindowEvent T D N K := by
-- proof
  apply StatMech.FrontierA.step3Distance_preimage_eq_iUnion_windows T D K

/--
[step3WindowMask_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3WindowMask_subset_box_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {q : FieldTriple d} :
-- imply
  step3WindowMask T D N q ⊆ boxFinsetBK d N := by
-- proof
  apply StatMech.FrontierA.step3WindowMask_subset_box T D N q

/--
[step3WindowMask_matches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3WindowMask_matches_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {q : FieldTriple d} :
-- imply
  step3MaskMatches T D N (step3WindowMask T D N q) q := by
-- proof
  apply StatMech.FrontierA.step3WindowMask_matches T D N q

/--
[coordinateBetween_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma coordinateBetween_mem_box_eq
  {d : ℕ}
  {x y z : Site d}
  {N : ℕ}
-- given
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hz : z ∈ coordinateBetween x y) :
-- imply
  z ∈ box d N := by
-- proof
  apply StatMech.FrontierA.coordinateBetween_mem_box hx hy hz

/--
[pairHighCluster_interpolatedHighPair_eq_siteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma pairHighCluster_interpolatedHighPair_eq_siteCluster_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d}
  {x : Site d} :
-- imply
  pairHighCluster (interpolatedHighPair T q) x = siteCluster (T q.2.2) x := by
-- proof
  apply StatMech.FrontierA.pairHighCluster_interpolatedHighPair_eq_siteCluster T q x

/--
[step3Contact_forceSet_subset_mask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3Contact_forceSet_subset_mask_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {q : FieldTriple d}
  {x y : Site d}
-- given
  (hxBox : x ∈ boxFinsetBK d N)
  (hyBox : y ∈ boxFinsetBK d N)
  (hxLow : x ∈ pairLowInfiniteVertices (interpolatedHighPair T q))
  (hxy : l1dist d x y = D) :
-- imply
  contactForceSet x y ⊆ step3WindowMask T D N q := by
-- proof
  apply StatMech.FrontierA.step3Contact_forceSet_subset_mask T D N q hxBox hyBox hxLow hxy

/--
[contactForceSet_l1dist_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma contactForceSet_l1dist_lt_eq
  {d : ℕ}
  {x y z : Site d}
  {D : ℕ}
-- given
  (hxy : l1dist d x y = D)
  (hz : z ∈ contactForceSet x y) :
-- imply
  l1dist d x z < D := by
-- proof
  apply StatMech.FrontierA.contactForceSet_l1dist_lt hxy hz

/--
[step3Deletion_cluster_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3Deletion_cluster_eq_original_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D : ℕ}
  {q : FieldTriple d}
  {S : Finset (Site d)}
-- given
  (hD : interpolatedHighPair T q ∈ pairStep3DistanceAt (0 : Site d) D)
  (hnear : ∀ z ∈ S, ∃ x ∈ pairLowInfiniteVertices (interpolatedHighPair T q), l1dist d x z < D) :
-- imply
  pairHighCluster (zeroHighPair T S q) 0 = pairHighCluster (interpolatedHighPair T q) 0 := by
-- proof
  apply StatMech.FrontierA.step3Deletion_cluster_eq_original T D q hD S hnear

/--
[step3Contact_gives_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3Contact_gives_source_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N : ℕ}
  {q : FieldTriple d}
  {x y : Site d}
-- given
  (hD : interpolatedHighPair T q ∈ pairStep3DistanceAt (0 : Site d) D)
  (hcontact : (x, y) ∈ step3WindowContacts T D N q) :
-- imply
  q ∈ step3SourceEvent T D N ((step3WindowMask T D N q, x), y) := by
-- proof
  apply StatMech.FrontierA.step3Contact_gives_source T D N q hD hcontact

/--
[step3CoreWindow_sourceDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3CoreWindow_sourceDegree_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {D N K : ℕ}
  {q : FieldTriple d}
-- given
  (hq : q ∈ step3CoreWindowEvent T D N K) :
-- imply
  K ≤ finiteEventMultiplicity (step3Indices (d := d) N) (step3SourceEvent T D N) q := by
-- proof
  apply StatMech.FrontierA.step3CoreWindow_sourceDegree T D N K q hq

/--
[step3CoreWindow_probability_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3CoreWindow_probability_bound_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
  {D N K : ℕ}
-- given
  (epsilon : ℝ≥0∞)
  (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
-- imply
  epsilon ^ (boxFinsetBK d D).card * K * mu (step3CoreWindowEvent T D N K) ≤ (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
-- proof
  apply StatMech.FrontierA.step3CoreWindow_probability_bound T mu D N K epsilon hinsert

/--
[step3Distance_probability_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3Distance_probability_bound_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
  {D K : ℕ}
-- given
  (epsilon : ℝ≥0∞)
  (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
-- imply
  epsilon ^ (boxFinsetBK d D).card * K * mu ((interpolatedHighPair T) ⁻¹' pairStep3DistanceAt (0 : Site d) D) ≤ (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
-- proof
  apply StatMech.FrontierA.step3Distance_probability_bound T mu D K epsilon hinsert

/--
[step3Distance_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma step3Distance_measure_zero_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
  {D : ℕ}
-- given
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
-- imply
  mu ((interpolatedHighPair T) ⁻¹' pairStep3DistanceAt (0 : Site d) D) = 0 := by
-- proof
  apply StatMech.FrontierA.step3Distance_measure_zero T mu D epsilon hepsilon hinsert

/--
[interpolatedHighPair_step3Core_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma interpolatedHighPair_step3Core_measure_zero_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
-- imply
  (interpolatedHighPairLaw T mu) (pairStep3CoreAt (0 : Site d)) = 0 := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPair_step3Core_measure_zero T mu epsilon hepsilon hinsert

/--
[monotoneAutomaton_infiniteCluster_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean)
-/
@[path]
private lemma monotoneAutomaton_infiniteCluster_uniqueness_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hd : 1 ≤ d)
  (herg : IsTripleFieldErgodic mu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsertMiddle : HasMiddleInsertionLowerBound mu T.threshold epsilon)
  (hinsertHigh : HasHighInsertionLowerBound mu T.threshold epsilon)
  (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
  (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
-- imply
  mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierA.monotoneAutomaton_infiniteCluster_uniqueness T mu hd herg epsilon hepsilon hinsertMiddle hinsertHigh hmono hlow


-- created on 2026-10-23
