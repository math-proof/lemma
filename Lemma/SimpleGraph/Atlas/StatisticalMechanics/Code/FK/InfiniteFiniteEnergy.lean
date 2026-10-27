import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
open MeasureTheory Set Filter Topology SimpleGraph StatMech StatMech.FK


/--
[boxRestrictLE_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma boxRestrictLE_setOpen_eq
  {d : ℕ}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {omega : ConfigSpace (Sym2 (boxVerts d m))}
-- given
  (hNm : N ≤ m) :
-- imply
  boxRestrictLE d hNm (setOpen (innerEdgeLE d hNm eb) omega) = setOpen eb (boxRestrictLE d hNm omega) := by
-- proof
  apply StatMech.FK.boxRestrictLE_setOpen hNm eb omega

/--
[boxRestrict_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma boxRestrict_setOpen_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {omega : ConfigSpace (Sym2 (Site d))} :
-- imply
  boxRestrict d N (setOpen (edgeIncl d N eb) omega) = setOpen eb (boxRestrict d N omega) := by
-- proof
  apply StatMech.FK.boxRestrict_setOpen N eb omega

/--
[boxRestrictLE_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma boxRestrictLE_setClosed_eq
  {d : ℕ}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {omega : ConfigSpace (Sym2 (boxVerts d m))}
-- given
  (hNm : N ≤ m) :
-- imply
  boxRestrictLE d hNm (setClosed (innerEdgeLE d hNm eb) omega) = setClosed eb (boxRestrictLE d hNm omega) := by
-- proof
  apply StatMech.FK.boxRestrictLE_setClosed hNm eb omega

/--
[boxRestrict_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma boxRestrict_setClosed_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {omega : ConfigSpace (Sym2 (Site d))} :
-- imply
  boxRestrict d N (setClosed (edgeIncl d N eb) omega) = setClosed eb (boxRestrict d N omega) := by
-- proof
  apply StatMech.FK.boxRestrict_setClosed N eb omega

/--
[wiredFinite_singleOpen_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredFinite_singleOpen_preimage_bound_eq
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤ (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.wiredFinite_singleOpen_preimage_bound N m hNm hp hp1 hq eb S

/--
[freeFinite_singleOpen_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeFinite_singleOpen_preimage_bound_eq
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤ (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.freeFinite_singleOpen_preimage_bound N m hNm hp hp1 hq eb S

/--
[wiredFinite_singleClosed_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredFinite_singleClosed_preimage_bound_eq
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤ (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.wiredFinite_singleClosed_preimage_bound N m hNm hp hp1 hq eb S

/--
[freeFinite_singleClosed_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeFinite_singleClosed_preimage_bound_eq
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤ (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.freeFinite_singleClosed_preimage_bound N m hNm hp hp1 hq eb S

/--
[wiredInfinite_singleOpen_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_singleOpen_cylinder_bound_eq
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.wiredInfinite_singleOpen_cylinder_bound N hp hp1 hq eb S

/--
[freeInfinite_singleOpen_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_singleOpen_cylinder_bound_eq
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.freeInfinite_singleOpen_cylinder_bound N hp hp1 hq eb S

/--
[wiredInfinite_singleClosed_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_singleClosed_cylinder_bound_eq
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.wiredInfinite_singleClosed_cylinder_bound N hp hp1 hq eb S

/--
[freeInfinite_singleClosed_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_singleClosed_cylinder_bound_eq
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.freeInfinite_singleClosed_cylinder_bound N hp hp1 hq eb S

/--
[setPattern_insert_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma setPattern_insert_eq_eq
  {d : ℕ}
  [DecidableEq V]
  {I : Finset (Sym2 V)}
  {e : Sym2 V}
  {eta : ConfigSpace ↥(insert e I)}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ I) :
-- imply
  let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩ setPattern (insert e I) eta psi = if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e (setPattern I etaI psi) else setClosed e (setPattern I etaI psi) := by
-- proof
  apply StatMech.FK.setPattern_insert_eq he eta psi

/--
[wiredInfinite_pattern_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_pattern_cylinder_bound_eq
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {I : Finset (Sym2 (boxVerts d N))}
  {eta : ConfigSpace ↥I}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setPattern I eta ⁻¹' S)) ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.wiredInfinite_pattern_cylinder_bound N hp hp1 hq I eta S

/--
[freeInfinite_pattern_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_pattern_cylinder_bound_eq
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {I : Finset (Sym2 (boxVerts d N))}
  {eta : ConfigSpace ↥I}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' (setPattern I eta ⁻¹' S)) ≤ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.freeInfinite_pattern_cylinder_bound N hp hp1 hq I eta S

/--
[liftPatternConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma liftPatternConfig_apply_eq
  {d : ℕ}
  {d : ℕ}
  {N M : ℕ}
  {I : Finset (Sym2 (boxVerts d N))}
  {eta : ConfigSpace ↥I}
  {e : Sym2 (boxVerts d N)}
-- given
  (hNM : N ≤ M)
  (he : e ∈ I) :
-- imply
  liftPatternConfig d hNM I eta ⟨innerEdgeLE d hNM e, by exact Finset.mem_map.mpr ⟨e, he, rfl⟩⟩ = eta ⟨e, he⟩ := by
-- proof
  apply StatMech.FK.liftPatternConfig_apply d hNM I eta e he

/--
[boxRestrictLE_setPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma boxRestrictLE_setPattern_eq
  {d : ℕ}
  {N M : ℕ}
  {I : Finset (Sym2 (boxVerts d N))}
  {eta : ConfigSpace ↥I}
  {omega : ConfigSpace (Sym2 (boxVerts d M))}
-- given
  (hNM : N ≤ M) :
-- imply
  boxRestrictLE d hNM (setPattern (liftPatternFinset d hNM I) (liftPatternConfig d hNM I eta) omega) = setPattern I eta (boxRestrictLE d hNM omega) := by
-- proof
  apply StatMech.FK.boxRestrictLE_setPattern hNM I eta omega

/--
[wiredInfinite_innerPattern_outerCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_innerPattern_outerCylinder_bound_eq
  {d : ℕ}
  {N M : ℕ}
  {p q : ℝ}
  {I : Finset (Sym2 (boxVerts d N))}
  {eta : ConfigSpace ↥I}
  {S : Set (ConfigSpace (Sym2 (boxVerts d M)))}
-- given
  (hNM : N ≤ M)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d M ⁻¹' (setPattern (liftPatternFinset d hNM I) (liftPatternConfig d hNM I eta) ⁻¹' S)) ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d M ⁻¹' S) := by
-- proof
  apply StatMech.FK.wiredInfinite_innerPattern_outerCylinder_bound N M hNM hp hp1 hq I eta S

/--
[freeInfinite_innerPattern_outerCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_innerPattern_outerCylinder_bound_eq
  {d : ℕ}
  {N M : ℕ}
  {p q : ℝ}
  {I : Finset (Sym2 (boxVerts d N))}
  {eta : ConfigSpace ↥I}
  {S : Set (ConfigSpace (Sym2 (boxVerts d M)))}
-- given
  (hNM : N ≤ M)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d M ⁻¹' (setPattern (liftPatternFinset d hNM I) (liftPatternConfig d hNM I eta) ⁻¹' S)) ≤ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d M ⁻¹' S) := by
-- proof
  apply StatMech.FK.freeInfinite_innerPattern_outerCylinder_bound N M hNM hp hp1 hq I eta S

/--
[cylinder_eq_boxRestrict_preimage_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma cylinder_eq_boxRestrict_preimage_extend_eq
  {d : ℕ}
  {N : ℕ}
  {s : Finset (Sym2 (Site d))}
  {S : Set (ConfigSpace ↥s)}
-- given
  (hs : ∀ e ∈ s, e ∈ Set.range (edgeIncl d N)) :
-- imply
  cylinder s S = boxRestrict d N ⁻¹' (extendEdge d N ⁻¹' cylinder s S) := by
-- proof
  apply StatMech.FK.cylinder_eq_boxRestrict_preimage_extend N s S hs

/--
[wiredInfinite_singleOpen_fullCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_singleOpen_fullCylinder_bound_eq
  {d : ℕ}
  {p q : ℝ}
  {e : Sym2 (Site d)}
  {C : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
-- imply
  cFE p q * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (setOpen e ⁻¹' C) ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
-- proof
  apply StatMech.FK.wiredInfinite_singleOpen_fullCylinder_bound hp hp1 hq e C hC

/--
[freeInfinite_singleOpen_fullCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_singleOpen_fullCylinder_bound_eq
  {d : ℕ}
  {p q : ℝ}
  {e : Sym2 (Site d)}
  {C : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
-- imply
  cFE p q * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (setOpen e ⁻¹' C) ≤ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
-- proof
  apply StatMech.FK.freeInfinite_singleOpen_fullCylinder_bound hp hp1 hq e C hC

/--
[wiredInfinite_singleClosed_fullCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_singleClosed_fullCylinder_bound_eq
  {d : ℕ}
  {p q : ℝ}
  {e : Sym2 (Site d)}
  {C : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
-- imply
  cFE p q * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (setClosed e ⁻¹' C) ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
-- proof
  apply StatMech.FK.wiredInfinite_singleClosed_fullCylinder_bound hp hp1 hq e C hC

/--
[freeInfinite_singleClosed_fullCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_singleClosed_fullCylinder_bound_eq
  {d : ℕ}
  {p q : ℝ}
  {e : Sym2 (Site d)}
  {C : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
-- imply
  cFE p q * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (setClosed e ⁻¹' C) ≤ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
-- proof
  apply StatMech.FK.freeInfinite_singleClosed_fullCylinder_bound hp hp1 hq e C hC

/--
[pattern_bound_of_cylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma pattern_bound_of_cylinders_eq
  {d : ℕ}
  [Countable E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {f : ConfigSpace E → ConfigSpace E}
  {c : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hf : Measurable f)
  (hc : 0 ≤ c)
  (hcyl : ∀ C ∈ measurableCylinders (fun _ : E => Bool), c * mu.real (f ⁻¹' C) ≤ mu.real C)
  (hA : MeasurableSet A) :
-- imply
  c * mu.real (f ⁻¹' A) ≤ mu.real A := by
-- proof
  apply StatMech.FK.pattern_bound_of_cylinders mu f hf c hc hcyl A hA

/--
[measurable_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma measurable_setOpen_eq
  {d : ℕ}
  [DecidableEq E]
  {e : E} :
-- imply
  Measurable (setOpen e : ConfigSpace E → ConfigSpace E) := by
-- proof
  apply StatMech.FK.measurable_setOpen e

/--
[measurable_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma measurable_setClosed_eq
  {d : ℕ}
  [DecidableEq E]
  {e : E} :
-- imply
  Measurable (setClosed e : ConfigSpace E → ConfigSpace E) := by
-- proof
  apply StatMech.FK.measurable_setClosed e

/--
[measurable_setPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma measurable_setPattern_eq
  {d : ℕ}
  [DecidableEq V]
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I} :
-- imply
  Measurable (setPattern I eta : ConfigSpace (Sym2 V) → ConfigSpace (Sym2 V)) := by
-- proof
  apply StatMech.FK.measurable_setPattern I eta

/--
[map_absolutelyContinuous_of_real_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma map_absolutelyContinuous_of_real_preimage_bound_eq
  {d : ℕ}
  [MeasurableSpace E]
  {mu : Measure E}
  [IsFiniteMeasure mu]
  {f : E → E}
  {c : ℝ}
-- given
  (hf : Measurable f)
  (hc : 0 < c)
  (hbound : ∀ A : Set E, MeasurableSet A → c * mu.real (f ⁻¹' A) ≤ mu.real A) :
-- imply
  mu.map f ≪ mu := by
-- proof
  apply StatMech.FK.map_absolutelyContinuous_of_real_preimage_bound mu f hf c hc hbound

/--
[wiredInfinite_setOpen_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_setOpen_absolutelyContinuous_eq
  {d : ℕ}
  {p q : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setOpen e) ≪ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.wiredInfinite_setOpen_absolutelyContinuous hp hp1 hq e

/--
[freeInfinite_setOpen_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_setOpen_absolutelyContinuous_eq
  {d : ℕ}
  {p q : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setOpen e) ≪ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.freeInfinite_setOpen_absolutelyContinuous hp hp1 hq e

/--
[wiredInfinite_setClosed_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_setClosed_absolutelyContinuous_eq
  {d : ℕ}
  {p q : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setClosed e) ≪ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.wiredInfinite_setClosed_absolutelyContinuous hp hp1 hq e

/--
[freeInfinite_setClosed_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_setClosed_absolutelyContinuous_eq
  {d : ℕ}
  {p q : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setClosed e) ≪ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.freeInfinite_setClosed_absolutelyContinuous hp hp1 hq e

/--
[setPattern_absolutelyContinuous_of_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma setPattern_absolutelyContinuous_of_single_eq
  {d : ℕ}
  [DecidableEq V]
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hopen : ∀ e : Sym2 V, mu.map (setOpen e) ≪ mu)
  (hclosed : ∀ e : Sym2 V, mu.map (setClosed e) ≪ mu) :
-- imply
  ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu := by
-- proof
  apply StatMech.FK.setPattern_absolutelyContinuous_of_single mu hopen hclosed

/--
[wiredInfinite_setPattern_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfinite_setPattern_absolutelyContinuous_eq
  {d : ℕ}
  {p q : ℝ}
  {I : Finset (Sym2 (Site d))}
  {eta : ConfigSpace ↥I}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setPattern I eta) ≪ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.wiredInfinite_setPattern_absolutelyContinuous hp hp1 hq I eta

/--
[freeInfinite_setPattern_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfinite_setPattern_absolutelyContinuous_eq
  {d : ℕ}
  {p q : ℝ}
  {I : Finset (Sym2 (Site d))}
  {eta : ConfigSpace ↥I}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setPattern I eta) ≪ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.freeInfinite_setPattern_absolutelyContinuous hp hp1 hq I eta

/--
[forceOpenFinset_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma forceOpenFinset_insert_eq
  {d : ℕ}
  {e : Sym2 (Site d)}
  {F : Finset (Sym2 (Site d))} :
-- imply
  StatMech.Percolation.forceOpenFinset (insert e F) = setOpen e ∘ StatMech.Percolation.forceOpenFinset F := by
-- proof
  apply StatMech.FK.forceOpenFinset_insert e F

/--
[hasFiniteEnergyMerge_of_singleOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma hasFiniteEnergyMerge_of_singleOpen_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hone : ∀ e : Sym2 (Site d), mu.map (setOpen e) ≪ mu) :
-- imply
  StatMech.Percolation.HasFiniteEnergyMerge mu := by
-- proof
  apply StatMech.FK.hasFiniteEnergyMerge_of_singleOpen mu hone

/--
[wiredInfiniteVolume_hasFiniteEnergyMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma wiredInfiniteVolume_hasFiniteEnergyMerge_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  StatMech.Percolation.HasFiniteEnergyMerge (d := d) (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_hasFiniteEnergyMerge hp hp1 hq

/--
[freeInfiniteVolume_hasFiniteEnergyMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean)
-/
@[path]
private lemma freeInfiniteVolume_hasFiniteEnergyMerge_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  StatMech.Percolation.HasFiniteEnergyMerge (d := d) (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_hasFiniteEnergyMerge hp hp1 hq


-- created on 2026-10-23
