import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
open StatMech StatMech.Exact3D StatMech.Exact3D.PolymerSupport StatMech.Exact3D.BoundedSite StatMech.Exact3D.BoundedPolymerCase


/--
[mem_translationCandidateSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma mem_translationCandidateSet_eq
  {d : ℕ}
  {P Q : PolymerSupport d}
  {v : Site d} :
-- imply
  v ∈ translationCandidateSet P Q ↔ ∃ y, y ∈ Q ∧ ∃ x, x ∈ P ∧ y - x = v := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.mem_translationCandidateSet P Q v

/--
[finiteTranslationEquivalent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma finiteTranslationEquivalent_iff_eq
  {d : ℕ}
  {P Q : PolymerSupport d} :
-- imply
  finiteTranslationEquivalent P Q ↔ ∃ v : Site d, Q = P.translate v := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.finiteTranslationEquivalent_iff P Q

/--
[cubicTransform_zero_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransform_zero_translate_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : CoordinateReflection d} :
-- imply
  (P.cubicTransform (0 : Site d) σ ε).translate v = P.cubicTransform v σ ε := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.cubicTransform_zero_translate P v σ ε

/--
[val_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma val_mem_box_eq
  {d R : ℕ}
  {x : BoundedSite d R} :
-- imply
  val x ∈ box d R := by
-- proof
  apply StatMech.Exact3D.BoundedSite.val_mem_box x

/--
[coordinateList_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coordinateList_injective_eq
  {d R : ℕ} :
-- imply
  Function.Injective (@coordinateList d R) := by
-- proof
  apply StatMech.Exact3D.BoundedSite.coordinateList_injective

/--
[supportKey_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma supportKey_toFinset_eq
  {d R : ℕ}
  {s : Finset (BoundedSite d R)} :
-- imply
  (supportKey s).toFinset = s.map (BoundedSite.coordinateEmbedding d R) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.supportKey_toFinset s

/--
[supportKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma supportKey_injective_eq
  {d R : ℕ} :
-- imply
  Function.Injective (@supportKey d R) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.supportKey_injective

/--
[stableKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma stableKey_injective_eq
  {d R maxDegree maxRange : ℕ} :
-- imply
  Function.Injective (@stableKey d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.stableKey_injective

/--
[mem_boundedSupportOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma mem_boundedSupportOf_eq
  {d R : ℕ}
  {P : PolymerSupport d}
  {x : BoundedSite d R}
-- given
  (hP : P.containedInBox R) :
-- imply
  x ∈ boundedSupportOf P hP ↔ x.1 ∈ P := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.mem_boundedSupportOf P hP x

/--
[boundedSupportOf_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma boundedSupportOf_card_eq
  {d R : ℕ}
  {P : PolymerSupport d}
-- given
  (hP : P.containedInBox R) :
-- imply
  (boundedSupportOf P hP).card = P.carrier.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.boundedSupportOf_card P hP

/--
[ofLocalCoordinate_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinate_support_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  (ofLocalCoordinate c hbox hdegree hrange).support = boundedSupportOf c.support hbox := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinate_support c hbox hdegree hrange

/--
[mem_ofLocalCoordinate_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma mem_ofLocalCoordinate_support_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {x : BoundedSite d R}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  x ∈ (ofLocalCoordinate c hbox hdegree hrange).support ↔ x.1 ∈ c.support := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.mem_ofLocalCoordinate_support c hbox hdegree hrange x

/--
[ofLocalCoordinate_degree_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinate_degree_val_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ((ofLocalCoordinate c hbox hdegree hrange).degree : ℕ) = c.degree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinate_degree_val c hbox hdegree hrange

/--
[ofLocalCoordinate_range_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinate_range_val_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ((ofLocalCoordinate c hbox hdegree hrange).range : ℕ) = c.range := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinate_range_val c hbox hdegree hrange

/--
[ofLocalCoordinate_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinate_support_card_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  (ofLocalCoordinate c hbox hdegree hrange).support.card = c.support.carrier.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinate_support_card c hbox hdegree hrange

/--
[classifyBoundedLocalCoordinate_degree_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma classifyBoundedLocalCoordinate_degree_val_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedLocalCoordinate d R maxDegree maxRange} :
-- imply
  ((classifyBoundedLocalCoordinate c).degree : ℕ) = c.1.degree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.classifyBoundedLocalCoordinate_degree_val c

/--
[classifyBoundedLocalCoordinate_range_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma classifyBoundedLocalCoordinate_range_val_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedLocalCoordinate d R maxDegree maxRange} :
-- imply
  ((classifyBoundedLocalCoordinate c).range : ℕ) = c.1.range := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.classifyBoundedLocalCoordinate_range_val c

/--
[mem_toPolymerSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma mem_toPolymerSupport_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange}
  {x : Site d} :
-- imply
  x ∈ c.toPolymerSupport ↔ ∃ y, y ∈ c.support ∧ BoundedSite.val y = x := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.mem_toPolymerSupport c x

/--
[boundedSite_val_mem_toPolymerSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma boundedSite_val_mem_toPolymerSupport_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange}
  {x : BoundedSite d R} :
-- imply
  BoundedSite.val x ∈ c.toPolymerSupport ↔ x ∈ c.support := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.boundedSite_val_mem_toPolymerSupport c x

/--
[toPolymerSupport_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma toPolymerSupport_card_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  c.toPolymerSupport.carrier.card = c.support.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.toPolymerSupport_card c

/--
[toPolymerSupport_containedInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma toPolymerSupport_containedInBox_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  c.toPolymerSupport.containedInBox R := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.toPolymerSupport_containedInBox c

/--
[toPolymerSupport_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma toPolymerSupport_coordinateDiameterBound_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  c.toPolymerSupport.coordinateDiameterBound (R + R) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.toPolymerSupport_coordinateDiameterBound c

/--
[toPolymerSupport_ofLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma toPolymerSupport_ofLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport = c.support := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.toPolymerSupport_ofLocalCoordinate c hbox hdegree hrange

/--
[mem_toPolymerSupport_ofLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma mem_toPolymerSupport_ofLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {x : Site d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  x ∈ (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport ↔ x ∈ c.support := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.mem_toPolymerSupport_ofLocalCoordinate c hbox hdegree hrange x

/--
[toPolymerSupport_ofLocalCoordinate_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma toPolymerSupport_ofLocalCoordinate_card_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport.carrier.card = c.support.carrier.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.toPolymerSupport_ofLocalCoordinate_card c hbox hdegree hrange

/--
[translateLocalCoordinate_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_support_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d} :
-- imply
  (translateLocalCoordinate c v).support = c.support.translate v := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_support c v

/--
[translateLocalCoordinate_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_degree_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d} :
-- imply
  (translateLocalCoordinate c v).degree = c.degree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_degree c v

/--
[translateLocalCoordinate_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_range_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d} :
-- imply
  (translateLocalCoordinate c v).range = c.range := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_range c v

/--
[translateLocalCoordinate_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_symmetry_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d} :
-- imply
  (translateLocalCoordinate c v).symmetry = c.symmetry := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_symmetry c v

/--
[translateLocalCoordinate_translationQuotiented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_translationQuotiented_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d} :
-- imply
  (translateLocalCoordinate c v).symmetry.translationQuotiented = c.symmetry.translationQuotiented := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_translationQuotiented c v

/--
[translateLocalCoordinate_cubicQuotiented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_cubicQuotiented_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d} :
-- imply
  (translateLocalCoordinate c v).symmetry.cubicQuotiented = c.symmetry.cubicQuotiented := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_cubicQuotiented c v

/--
[translateLocalCoordinate_spinFlipEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_spinFlipEven_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d} :
-- imply
  (translateLocalCoordinate c v).symmetry.spinFlipEven = c.symmetry.spinFlipEven := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_spinFlipEven c v

/--
[translateLocalCoordinate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_zero_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d} :
-- imply
  translateLocalCoordinate c (0 : Site d) = c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_zero c

/--
[translateLocalCoordinate_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_translate_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v w : Site d} :
-- imply
  translateLocalCoordinate (translateLocalCoordinate c v) w = translateLocalCoordinate c (v + w) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_translate c v w

/--
[translateLocalCoordinate_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_support_card_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d} :
-- imply
  (translateLocalCoordinate c v).support.carrier.card = c.support.carrier.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_support_card c v

/--
[translateLocalCoordinate_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translateLocalCoordinate_coordinateDiameterBound_eq
  {d R : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
-- given
  (hdiam : c.support.coordinateDiameterBound R) :
-- imply
  (translateLocalCoordinate c v).support.coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translateLocalCoordinate_coordinateDiameterBound c v hdiam

/--
[permuteLocalCoordinate_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_support_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (permuteLocalCoordinate c σ).support = c.support.permuteCoordinates σ := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_support c σ

/--
[permuteLocalCoordinate_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_degree_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (permuteLocalCoordinate c σ).degree = c.degree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_degree c σ

/--
[permuteLocalCoordinate_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_range_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (permuteLocalCoordinate c σ).range = c.range := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_range c σ

/--
[permuteLocalCoordinate_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_symmetry_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (permuteLocalCoordinate c σ).symmetry = c.symmetry := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_symmetry c σ

/--
[permuteLocalCoordinate_translationQuotiented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_translationQuotiented_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (permuteLocalCoordinate c σ).symmetry.translationQuotiented = c.symmetry.translationQuotiented := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_translationQuotiented c σ

/--
[permuteLocalCoordinate_cubicQuotiented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_cubicQuotiented_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (permuteLocalCoordinate c σ).symmetry.cubicQuotiented = c.symmetry.cubicQuotiented := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_cubicQuotiented c σ

/--
[permuteLocalCoordinate_spinFlipEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_spinFlipEven_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (permuteLocalCoordinate c σ).symmetry.spinFlipEven = c.symmetry.spinFlipEven := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_spinFlipEven c σ

/--
[permuteLocalCoordinate_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_refl_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d} :
-- imply
  permuteLocalCoordinate c (Equiv.refl (Fin d)) = c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_refl c

/--
[permuteLocalCoordinate_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_trans_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ τ : Equiv.Perm (Fin d)} :
-- imply
  permuteLocalCoordinate (permuteLocalCoordinate c σ) τ = permuteLocalCoordinate c (σ.trans τ) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_trans c σ τ

/--
[permuteLocalCoordinate_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_support_card_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (permuteLocalCoordinate c σ).support.carrier.card = c.support.carrier.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_support_card c σ

/--
[permuteLocalCoordinate_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_coordinateDiameterBound_eq
  {d R : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)}
-- given
  (hdiam : c.support.coordinateDiameterBound R) :
-- imply
  (permuteLocalCoordinate c σ).support.coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_coordinateDiameterBound c σ hdiam

/--
[permuteLocalCoordinate_containedInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma permuteLocalCoordinate_containedInBox_eq
  {d R : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)}
-- given
  (hbox : c.support.containedInBox R) :
-- imply
  (permuteLocalCoordinate c σ).support.containedInBox R := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.permuteLocalCoordinate_containedInBox c σ hbox

/--
[reflectLocalCoordinate_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_support_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (reflectLocalCoordinate c ε).support = c.support.reflectCoordinates ε := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_support c ε

/--
[reflectLocalCoordinate_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_degree_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (reflectLocalCoordinate c ε).degree = c.degree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_degree c ε

/--
[reflectLocalCoordinate_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_range_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (reflectLocalCoordinate c ε).range = c.range := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_range c ε

/--
[reflectLocalCoordinate_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_symmetry_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (reflectLocalCoordinate c ε).symmetry = c.symmetry := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_symmetry c ε

/--
[reflectLocalCoordinate_translationQuotiented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_translationQuotiented_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (reflectLocalCoordinate c ε).symmetry.translationQuotiented = c.symmetry.translationQuotiented := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_translationQuotiented c ε

/--
[reflectLocalCoordinate_cubicQuotiented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_cubicQuotiented_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (reflectLocalCoordinate c ε).symmetry.cubicQuotiented = c.symmetry.cubicQuotiented := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_cubicQuotiented c ε

/--
[reflectLocalCoordinate_spinFlipEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_spinFlipEven_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (reflectLocalCoordinate c ε).symmetry.spinFlipEven = c.symmetry.spinFlipEven := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_spinFlipEven c ε

/--
[reflectLocalCoordinate_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_false_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d} :
-- imply
  reflectLocalCoordinate c (fun _ : Fin d => false) = c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_false c

/--
[reflectLocalCoordinate_reflectLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_reflectLocalCoordinate_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε δ : PolymerSupport.CoordinateReflection d} :
-- imply
  reflectLocalCoordinate (reflectLocalCoordinate c ε) δ = reflectLocalCoordinate c (fun i => Bool.xor (ε i) (δ i)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_reflectLocalCoordinate c ε δ

/--
[reflectLocalCoordinate_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_support_card_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (reflectLocalCoordinate c ε).support.carrier.card = c.support.carrier.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_support_card c ε

/--
[reflectLocalCoordinate_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_coordinateDiameterBound_eq
  {d R : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hdiam : c.support.coordinateDiameterBound R) :
-- imply
  (reflectLocalCoordinate c ε).support.coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_coordinateDiameterBound c ε hdiam

/--
[reflectLocalCoordinate_containedInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma reflectLocalCoordinate_containedInBox_eq
  {d R : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R) :
-- imply
  (reflectLocalCoordinate c ε).support.containedInBox R := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.reflectLocalCoordinate_containedInBox c ε hbox

/--
[cubicTransformLocalCoordinate_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_support_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).support = c.support.cubicTransform v σ ε := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_support c v σ ε

/--
[cubicTransformLocalCoordinate_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_degree_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).degree = c.degree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_degree c v σ ε

/--
[cubicTransformLocalCoordinate_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_range_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).range = c.range := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_range c v σ ε

/--
[cubicTransformLocalCoordinate_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_symmetry_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).symmetry = c.symmetry := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_symmetry c v σ ε

/--
[cubicTransformLocalCoordinate_translationQuotiented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_translationQuotiented_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).symmetry.translationQuotiented = c.symmetry.translationQuotiented := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_translationQuotiented c v σ ε

/--
[cubicTransformLocalCoordinate_cubicQuotiented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_cubicQuotiented_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).symmetry.cubicQuotiented = c.symmetry.cubicQuotiented := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_cubicQuotiented c v σ ε

/--
[cubicTransformLocalCoordinate_spinFlipEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_spinFlipEven_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).symmetry.spinFlipEven = c.symmetry.spinFlipEven := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_spinFlipEven c v σ ε

/--
[cubicTransformLocalCoordinate_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_identity_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d} :
-- imply
  cubicTransformLocalCoordinate c (0 : Site d) (Equiv.refl (Fin d)) (fun _ : Fin d => false) = c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_identity c

/--
[cubicTransformLocalCoordinate_cubicTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_cubicTransform_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v w : Site d}
  {σ τ : Equiv.Perm (Fin d)}
  {ε δ : PolymerSupport.CoordinateReflection d} :
-- imply
  cubicTransformLocalCoordinate (cubicTransformLocalCoordinate c v σ ε) w τ δ = cubicTransformLocalCoordinate c (PolymerSupport.reflectCoordinatesSite δ (PolymerSupport.permuteCoordinatesSite τ v) + w) (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_cubicTransform c v w σ τ ε δ

/--
[cubicTransformLocalCoordinate_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_support_card_eq
  {d : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d} :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).support.carrier.card = c.support.carrier.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_support_card c v σ ε

/--
[cubicTransformLocalCoordinate_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_coordinateDiameterBound_eq
  {d R : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hdiam : c.support.coordinateDiameterBound R) :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).support.coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_coordinateDiameterBound c v σ ε hdiam

/--
[cubicTransformLocalCoordinate_containedInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicTransformLocalCoordinate_containedInBox_eq
  {d R S : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R)
  (hv : PolymerSupport.coordinateRadiusBound S v) :
-- imply
  (cubicTransformLocalCoordinate c v σ ε).support.containedInBox (R + S) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicTransformLocalCoordinate_containedInBox c v σ ε hbox hv

/--
[ofLocalCoordinateAnchoredAt_degree_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinateAnchoredAt_degree_val_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {a : Site d}
-- given
  (ha : a ∈ c.support)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ((ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).degree : ℕ) = c.degree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinateAnchoredAt_degree_val c ha hdiam hdegree hrange

/--
[ofLocalCoordinateAnchoredAt_range_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinateAnchoredAt_range_val_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {a : Site d}
-- given
  (ha : a ∈ c.support)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ((ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).range : ℕ) = c.range := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinateAnchoredAt_range_val c ha hdiam hdegree hrange

/--
[toPolymerSupport_ofLocalCoordinateAnchoredAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma toPolymerSupport_ofLocalCoordinateAnchoredAt_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {a : Site d}
-- given
  (ha : a ∈ c.support)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  (ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).toPolymerSupport = c.support.translate (-a) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.toPolymerSupport_ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange

/--
[exists_boundedCase_translate_of_nonempty_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exists_boundedCase_translate_of_nonempty_coordinateDiameterBound_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hne : c.support.carrier.Nonempty)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange), ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧ bc.toPolymerSupport = c.support.translate v := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exists_boundedCase_translate_of_nonempty_coordinateDiameterBound c hne hdiam hdegree hrange

/--
[translationEquivalent_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translationEquivalent_refl_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  translationEquivalent c c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translationEquivalent_refl c

/--
[translationEquivalent_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translationEquivalent_symm_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : translationEquivalent c c') :
-- imply
  translationEquivalent c' c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translationEquivalent_symm h

/--
[translationEquivalent_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma translationEquivalent_trans_eq
  {d R maxDegree maxRange : ℕ}
  {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h₁₂ : translationEquivalent c₁ c₂)
  (h₂₃ : translationEquivalent c₂ c₃) :
-- imply
  translationEquivalent c₁ c₃ := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.translationEquivalent_trans h₁₂ h₂₃

/--
[exhaustiveTranslationClassTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exhaustiveTranslationClassTable_covers_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  translationClass c ∈ exhaustiveTranslationClassTable d R maxDegree maxRange := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exhaustiveTranslationClassTable_covers d R maxDegree maxRange c

/--
[coordinatePermutationEquivalent_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coordinatePermutationEquivalent_refl_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  coordinatePermutationEquivalent c c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.coordinatePermutationEquivalent_refl c

/--
[coordinatePermutationEquivalent_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coordinatePermutationEquivalent_symm_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : coordinatePermutationEquivalent c c') :
-- imply
  coordinatePermutationEquivalent c' c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.coordinatePermutationEquivalent_symm h

/--
[coordinatePermutationEquivalent_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coordinatePermutationEquivalent_trans_eq
  {d R maxDegree maxRange : ℕ}
  {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h₁₂ : coordinatePermutationEquivalent c₁ c₂)
  (h₂₃ : coordinatePermutationEquivalent c₂ c₃) :
-- imply
  coordinatePermutationEquivalent c₁ c₃ := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.coordinatePermutationEquivalent_trans h₁₂ h₂₃

/--
[exhaustiveCoordinatePermutationClassTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exhaustiveCoordinatePermutationClassTable_covers_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  coordinatePermutationClass c ∈ exhaustiveCoordinatePermutationClassTable d R maxDegree maxRange := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exhaustiveCoordinatePermutationClassTable_covers d R maxDegree maxRange c

/--
[coordinateReflectionEquivalent_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coordinateReflectionEquivalent_refl_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  coordinateReflectionEquivalent c c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.coordinateReflectionEquivalent_refl c

/--
[coordinateReflectionEquivalent_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coordinateReflectionEquivalent_symm_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : coordinateReflectionEquivalent c c') :
-- imply
  coordinateReflectionEquivalent c' c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.coordinateReflectionEquivalent_symm h

/--
[coordinateReflectionEquivalent_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coordinateReflectionEquivalent_trans_eq
  {d R maxDegree maxRange : ℕ}
  {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h₁₂ : coordinateReflectionEquivalent c₁ c₂)
  (h₂₃ : coordinateReflectionEquivalent c₂ c₃) :
-- imply
  coordinateReflectionEquivalent c₁ c₃ := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.coordinateReflectionEquivalent_trans h₁₂ h₂₃

/--
[exhaustiveCoordinateReflectionClassTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exhaustiveCoordinateReflectionClassTable_covers_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  coordinateReflectionClass c ∈ exhaustiveCoordinateReflectionClassTable d R maxDegree maxRange := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exhaustiveCoordinateReflectionClassTable_covers d R maxDegree maxRange c

/--
[cubicEquivalent_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicEquivalent_refl_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  cubicEquivalent c c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicEquivalent_refl c

/--
[cubicEquivalent_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicEquivalent_support_card_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : cubicEquivalent c c') :
-- imply
  c'.support.card = c.support.card := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicEquivalent_support_card h

/--
[cubicEquivalent_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicEquivalent_coordinateDiameterBound_eq
  {d R maxDegree maxRange D : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : cubicEquivalent c c')
  (hdiam : c.toPolymerSupport.coordinateDiameterBound D) :
-- imply
  c'.toPolymerSupport.coordinateDiameterBound D := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicEquivalent_coordinateDiameterBound h hdiam

/--
[cubicEquivalent_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicEquivalent_symm_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : cubicEquivalent c c') :
-- imply
  cubicEquivalent c' c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicEquivalent_symm h

/--
[cubicEquivalent_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicEquivalent_trans_eq
  {d R maxDegree maxRange : ℕ}
  {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h₁₂ : cubicEquivalent c₁ c₂)
  (h₂₃ : cubicEquivalent c₂ c₃) :
-- imply
  cubicEquivalent c₁ c₃ := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicEquivalent_trans h₁₂ h₂₃

/--
[ofLocalCoordinate_cubicTransformLocalCoordinate_cubicEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinate_cubicTransformLocalCoordinate_cubicEquivalent_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R)
  (hbox' : (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  cubicEquivalent (ofLocalCoordinate c hbox hdegree hrange) (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε) hbox' (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinate_cubicTransformLocalCoordinate_cubicEquivalent c v σ ε hbox hbox' hdegree hrange

/--
[ofLocalCoordinate_permuteLocalCoordinate_cubicEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinate_permuteLocalCoordinate_cubicEquivalent_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  cubicEquivalent (ofLocalCoordinate c hbox hdegree hrange) (ofLocalCoordinate (permuteLocalCoordinate c σ) (permuteLocalCoordinate_containedInBox c σ hbox) (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinate_permuteLocalCoordinate_cubicEquivalent c σ hbox hdegree hrange

/--
[ofLocalCoordinate_reflectLocalCoordinate_cubicEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma ofLocalCoordinate_reflectLocalCoordinate_cubicEquivalent_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  cubicEquivalent (ofLocalCoordinate c hbox hdegree hrange) (ofLocalCoordinate (reflectLocalCoordinate c ε) (reflectLocalCoordinate_containedInBox c ε hbox) (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ofLocalCoordinate_reflectLocalCoordinate_cubicEquivalent c ε hbox hdegree hrange

/--
[finiteCubicEquivalent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma finiteCubicEquivalent_iff_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  finiteCubicEquivalent c c' ↔ cubicEquivalent c c' := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.finiteCubicEquivalent_iff c c'

/--
[cubicClass_ofLocalCoordinate_cubicTransformLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicClass_ofLocalCoordinate_cubicTransformLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R)
  (hbox' : (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  cubicClass (ofLocalCoordinate c hbox hdegree hrange) = cubicClass (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε) hbox' (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicClass_ofLocalCoordinate_cubicTransformLocalCoordinate c v σ ε hbox hbox' hdegree hrange

/--
[cubicClass_ofLocalCoordinate_permuteLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicClass_ofLocalCoordinate_permuteLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  cubicClass (ofLocalCoordinate c hbox hdegree hrange) = cubicClass (ofLocalCoordinate (permuteLocalCoordinate c σ) (permuteLocalCoordinate_containedInBox c σ hbox) (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicClass_ofLocalCoordinate_permuteLocalCoordinate c σ hbox hdegree hrange

/--
[cubicClass_ofLocalCoordinate_reflectLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicClass_ofLocalCoordinate_reflectLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  cubicClass (ofLocalCoordinate c hbox hdegree hrange) = cubicClass (ofLocalCoordinate (reflectLocalCoordinate c ε) (reflectLocalCoordinate_containedInBox c ε hbox) (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicClass_ofLocalCoordinate_reflectLocalCoordinate c ε hbox hdegree hrange

/--
[cubicRepresentative_class](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicRepresentative_class_eq
  {d R maxDegree maxRange : ℕ}
  {q : CubicClass d R maxDegree maxRange} :
-- imply
  cubicClass (cubicRepresentative q) = q := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicRepresentative_class q

/--
[cubicRepresentative_equivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicRepresentative_equivalent_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  cubicEquivalent (cubicRepresentative (cubicClass c)) c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicRepresentative_equivalent c

/--
[mem_cubicOrbitFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma mem_cubicOrbitFiber_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  c' ∈ cubicOrbitFiber c ↔ cubicEquivalent c' c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.mem_cubicOrbitFiber

/--
[cubicOrbitFiber_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicOrbitFiber_nonempty_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  (cubicOrbitFiber c).Nonempty := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicOrbitFiber_nonempty c

/--
[cubicOrbitFiber_eq_of_equivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicOrbitFiber_eq_of_equivalent_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : cubicEquivalent c c') :
-- imply
  cubicOrbitFiber c = cubicOrbitFiber c' := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicOrbitFiber_eq_of_equivalent h

/--
[minimalCubicRepresentativeOfCase_eq_of_equivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma minimalCubicRepresentativeOfCase_eq_of_equivalent_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : cubicEquivalent c c') :
-- imply
  minimalCubicRepresentativeOfCase c = minimalCubicRepresentativeOfCase c' := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.minimalCubicRepresentativeOfCase_eq_of_equivalent h

/--
[minimalCubicRepresentative_class](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma minimalCubicRepresentative_class_eq
  {d R maxDegree maxRange : ℕ}
  {q : CubicClass d R maxDegree maxRange} :
-- imply
  cubicClass (minimalCubicRepresentative q) = q := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.minimalCubicRepresentative_class q

/--
[exhaustiveCubicClassTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exhaustiveCubicClassTable_covers_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  cubicClass c ∈ exhaustiveCubicClassTable d R maxDegree maxRange := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exhaustiveCubicClassTable_covers d R maxDegree maxRange c

/--
[exhaustiveTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exhaustiveTable_covers_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  c ∈ exhaustiveTable d R maxDegree maxRange := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exhaustiveTable_covers d R maxDegree maxRange c

/--
[exhaustiveTable_covers_localCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exhaustiveTable_covers_localCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ofLocalCoordinate c hbox hdegree hrange ∈ exhaustiveTable d R maxDegree maxRange := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exhaustiveTable_covers_localCoordinate c hbox hdegree hrange

/--
[exhaustiveTable_covers_diameterLocalCoordinate_after_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exhaustiveTable_covers_diameterLocalCoordinate_after_translate_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
-- given
  (hne : c.support.carrier.Nonempty)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange), bc ∈ exhaustiveTable d R maxDegree maxRange ∧ ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧ bc.toPolymerSupport = c.support.translate v := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exhaustiveTable_covers_diameterLocalCoordinate_after_translate c hne hdiam hdegree hrange

/--
[exhaustiveTable_covers_boundedLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma exhaustiveTable_covers_boundedLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedLocalCoordinate d R maxDegree maxRange} :
-- imply
  classifyBoundedLocalCoordinate c ∈ exhaustiveTable d R maxDegree maxRange := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exhaustiveTable_covers_boundedLocalCoordinate c

/--
[caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
-- given
  (hT : exhaustiveTable d R maxDegree maxRange ⊆ T.cases) :
-- imply
  RatInterval.CaseTable.Covers T (@classifyBoundedLocalCoordinate d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset T hT

/--
[caseTable_covers_and_sound_boundedLocalCoordinate_of_caseValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma caseTable_covers_and_sound_boundedLocalCoordinate_of_caseValue_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hcover : exhaustiveTable d R maxDegree maxRange ⊆ T.cases)
  (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
  (hcase : ∀ k, k ∈ T.cases → (T.interval k).MemR (caseValue k)) :
-- imply
  RatInterval.CaseTable.Covers T (@classifyBoundedLocalCoordinate d R maxDegree maxRange) ∧ RatInterval.CaseTable.Sound T (@classifyBoundedLocalCoordinate d R maxDegree maxRange) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.caseTable_covers_and_sound_boundedLocalCoordinate_of_caseValue T value caseValue hcover hvalue hcase

/--
[generatedIntervalTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedIntervalTable_covers_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval} :
-- imply
  RatInterval.CaseTable.Covers (generatedIntervalTable intervalOf) id := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedIntervalTable_covers intervalOf

/--
[generatedIntervalTable_covers_diameterLocalCoordinate_after_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedIntervalTable_covers_diameterLocalCoordinate_after_translate_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval}
  {c : LocalPolymerCoordinate d}
-- given
  (hne : c.support.carrier.Nonempty)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange), bc ∈ (generatedIntervalTable intervalOf).cases ∧ ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧ bc.toPolymerSupport = c.support.translate v := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedIntervalTable_covers_diameterLocalCoordinate_after_translate intervalOf c hne hdiam hdegree hrange

/--
[generatedIntervalTable_sound_of_caseValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedIntervalTable_sound_of_caseValue_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hcase : ∀ c, (intervalOf c).MemR (caseValue c)) :
-- imply
  RatInterval.CaseTable.Sound (generatedIntervalTable intervalOf) id caseValue := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedIntervalTable_sound_of_caseValue intervalOf caseValue hcase

/--
[generatedIntervalTable_covers_and_sound_boundedLocalCoordinate_of_caseValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedIntervalTable_covers_and_sound_boundedLocalCoordinate_of_caseValue_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
  (hcase : ∀ c, (intervalOf c).MemR (caseValue c)) :
-- imply
  RatInterval.CaseTable.Covers (generatedIntervalTable intervalOf) (@classifyBoundedLocalCoordinate d R maxDegree maxRange) ∧ RatInterval.CaseTable.Sound (generatedIntervalTable intervalOf) (@classifyBoundedLocalCoordinate d R maxDegree maxRange) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedIntervalTable_covers_and_sound_boundedLocalCoordinate_of_caseValue intervalOf value caseValue hvalue hcase

/--
[generatedStableKeyIntervalTable_covers_boundedCase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedStableKeyIntervalTable_covers_boundedCase_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval} :
-- imply
  RatInterval.CaseTable.Covers (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf) (@stableKey d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedStableKeyIntervalTable_covers_boundedCase intervalOf

/--
[generatedStableKeyIntervalTable_covers_diameterLocalCoordinate_after_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedStableKeyIntervalTable_covers_diameterLocalCoordinate_after_translate_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {c : LocalPolymerCoordinate d}
-- given
  (hne : c.support.carrier.Nonempty)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange), stableKey bc ∈ (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf).cases ∧ ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧ bc.toPolymerSupport = c.support.translate v := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedStableKeyIntervalTable_covers_diameterLocalCoordinate_after_translate intervalOf c hne hdiam hdegree hrange

/--
[generatedStableKeyIntervalTable_sound_boundedCase_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedStableKeyIntervalTable_sound_boundedCase_of_keyValue_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, caseValue c = keyValue (stableKey c))
  (hkey : ∀ k, k ∈ (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf).cases → (intervalOf k).MemR (keyValue k)) :
-- imply
  RatInterval.CaseTable.Sound (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf) (@stableKey d R maxDegree maxRange) caseValue := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedStableKeyIntervalTable_sound_boundedCase_of_keyValue intervalOf caseValue keyValue hvalue hkey

/--
[generatedStableKeyTable_covers_and_sound_boundedLocal_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedStableKeyTable_covers_and_sound_boundedLocal_of_keyValue_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, value c = keyValue (stableKey (classifyBoundedLocalCoordinate c)))
  (hkey : ∀ k, k ∈ (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf).cases → (intervalOf k).MemR (keyValue k)) :
-- imply
  RatInterval.CaseTable.Covers (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => stableKey (classifyBoundedLocalCoordinate c)) ∧ RatInterval.CaseTable.Sound (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => stableKey (classifyBoundedLocalCoordinate c)) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedStableKeyTable_covers_and_sound_boundedLocal_of_keyValue intervalOf value keyValue hvalue hkey

/--
[generatedCubicIntervalTable_covers_boundedCase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedCubicIntervalTable_covers_boundedCase_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : CubicClass d R maxDegree maxRange → RatInterval} :
-- imply
  RatInterval.CaseTable.Covers (generatedCubicIntervalTable intervalOf) (@cubicClass d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedCubicIntervalTable_covers_boundedCase intervalOf

/--
[generatedCubicIntervalTable_covers_diameterLocalCoordinate_after_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedCubicIntervalTable_covers_diameterLocalCoordinate_after_translate_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : CubicClass d R maxDegree maxRange → RatInterval}
  {c : LocalPolymerCoordinate d}
-- given
  (hne : c.support.carrier.Nonempty)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange), cubicClass bc ∈ (generatedCubicIntervalTable intervalOf).cases ∧ ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧ bc.toPolymerSupport = c.support.translate v := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedCubicIntervalTable_covers_diameterLocalCoordinate_after_translate intervalOf c hne hdiam hdegree hrange

/--
[generatedCubicIntervalTable_covers_boundedLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedCubicIntervalTable_covers_boundedLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : CubicClass d R maxDegree maxRange → RatInterval} :
-- imply
  RatInterval.CaseTable.Covers (generatedCubicIntervalTable intervalOf) (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedCubicIntervalTable_covers_boundedLocalCoordinate intervalOf

/--
[generatedCubicIntervalTable_sound_boundedCase_of_classValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedCubicIntervalTable_sound_boundedCase_of_classValue_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : CubicClass d R maxDegree maxRange → RatInterval}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
  {classValue : CubicClass d R maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, caseValue c = classValue (cubicClass c))
  (hclass : ∀ q, (intervalOf q).MemR (classValue q)) :
-- imply
  RatInterval.CaseTable.Sound (generatedCubicIntervalTable intervalOf) (@cubicClass d R maxDegree maxRange) caseValue := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedCubicIntervalTable_sound_boundedCase_of_classValue intervalOf caseValue classValue hvalue hclass

/--
[generatedCubicIntervalTable_covers_and_sound_boundedLocalCoordinate_of_classValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedCubicIntervalTable_covers_and_sound_boundedLocalCoordinate_of_classValue_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : CubicClass d R maxDegree maxRange → RatInterval}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {classValue : CubicClass d R maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, value c = classValue (classifyBoundedLocalCoordinateCubicClass c))
  (hclass : ∀ q, (intervalOf q).MemR (classValue q)) :
-- imply
  RatInterval.CaseTable.Covers (generatedCubicIntervalTable intervalOf) (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) ∧ RatInterval.CaseTable.Sound (generatedCubicIntervalTable intervalOf) (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedCubicIntervalTable_covers_and_sound_boundedLocalCoordinate_of_classValue intervalOf value classValue hvalue hclass

/--
[classifyByCubicRepresentative_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma classifyByCubicRepresentative_mem_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
  {c : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (hcover : CubicRepresentativeTableCovers T) :
-- imply
  classifyByCubicRepresentative T hcover c ∈ T.cases := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.classifyByCubicRepresentative_mem T hcover c

/--
[classifyByCubicRepresentative_equivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma classifyByCubicRepresentative_equivalent_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
  {c : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (hcover : CubicRepresentativeTableCovers T) :
-- imply
  cubicEquivalent (classifyByCubicRepresentative T hcover c) c := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.classifyByCubicRepresentative_equivalent T hcover c

/--
[cubicRepresentativeTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicRepresentativeTable_covers_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
-- given
  (hcover : CubicRepresentativeTableCovers T) :
-- imply
  RatInterval.CaseTable.Covers T (classifyByCubicRepresentative T hcover) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicRepresentativeTable_covers T hcover

/--
[cubicRepresentativeTable_sound_of_cubicInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicRepresentativeTable_sound_of_cubicInvariant_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hcover : CubicRepresentativeTableCovers T)
  (hinv : ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
  (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
-- imply
  RatInterval.CaseTable.Sound T (classifyByCubicRepresentative T hcover) caseValue := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicRepresentativeTable_sound_of_cubicInvariant T hcover caseValue hinv hcase

/--
[cubicRepresentativeTable_covers_and_sound_of_cubicInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicRepresentativeTable_covers_and_sound_of_cubicInvariant_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hcover : CubicRepresentativeTableCovers T)
  (hinv : ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
  (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
-- imply
  RatInterval.CaseTable.Covers T (classifyByCubicRepresentative T hcover) ∧ RatInterval.CaseTable.Sound T (classifyByCubicRepresentative T hcover) caseValue := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicRepresentativeTable_covers_and_sound_of_cubicInvariant T hcover caseValue hinv hcase

/--
[cubicRepresentativeTable_covers_boundedLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicRepresentativeTable_covers_boundedLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
-- given
  (hcover : CubicRepresentativeTableCovers T) :
-- imply
  RatInterval.CaseTable.Covers T (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicRepresentativeTable_covers_boundedLocalCoordinate T hcover

/--
[cubicRepresentativeTable_covers_and_sound_boundedLocalCoordinate_of_cubicInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma cubicRepresentativeTable_covers_and_sound_boundedLocalCoordinate_of_cubicInvariant_eq
  {d R maxDegree maxRange : ℕ}
  {T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hcover : CubicRepresentativeTableCovers T)
  (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
  (hinv : ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
  (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
-- imply
  RatInterval.CaseTable.Covers T (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) ∧ RatInterval.CaseTable.Sound T (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.cubicRepresentativeTable_covers_and_sound_boundedLocalCoordinate_of_cubicInvariant T hcover value caseValue hvalue hinv hcase

/--
[generatedMinimalCubicRepresentativeTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedMinimalCubicRepresentativeTable_covers_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval} :
-- imply
  CubicRepresentativeTableCovers (generatedMinimalCubicRepresentativeTable intervalOf) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedMinimalCubicRepresentativeTable_covers intervalOf

/--
[generatedMinimalCubicRepresentativeTable_covers_diameterLocalCoordinate_after_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedMinimalCubicRepresentativeTable_covers_diameterLocalCoordinate_after_translate_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval}
  {c : LocalPolymerCoordinate d}
-- given
  (hne : c.support.carrier.Nonempty)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ∃ (v : Site d) (bc r : BoundedPolymerCase d R maxDegree maxRange), r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases ∧ cubicEquivalent r bc ∧ ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧ bc.toPolymerSupport = c.support.translate v := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedMinimalCubicRepresentativeTable_covers_diameterLocalCoordinate_after_translate intervalOf c hne hdiam hdegree hrange

/--
[generatedMinimalCubicRepresentativeTable_covers_and_sound_of_cubicInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedMinimalCubicRepresentativeTable_covers_and_sound_of_cubicInvariant_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hinv : ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
  (hcase : ∀ r, r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases → (intervalOf r).MemR (caseValue r)) :
-- imply
  RatInterval.CaseTable.Covers (generatedMinimalCubicRepresentativeTable intervalOf) (classifyByCubicRepresentative (generatedMinimalCubicRepresentativeTable intervalOf) (generatedMinimalCubicRepresentativeTable_covers intervalOf)) ∧ RatInterval.CaseTable.Sound (generatedMinimalCubicRepresentativeTable intervalOf) (classifyByCubicRepresentative (generatedMinimalCubicRepresentativeTable intervalOf) (generatedMinimalCubicRepresentativeTable_covers intervalOf)) caseValue := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedMinimalCubicRepresentativeTable_covers_and_sound_of_cubicInvariant intervalOf caseValue hinv hcase

/--
[minimalRepTable_covers_and_sound_boundedLocal_of_cubicInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma minimalRepTable_covers_and_sound_boundedLocal_of_cubicInvariant_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
  (hinv : ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
  (hcase : ∀ r, r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases → (intervalOf r).MemR (caseValue r)) :
-- imply
  RatInterval.CaseTable.Covers (generatedMinimalCubicRepresentativeTable intervalOf) (classifyBoundedLocalCoordinateByCubicRepresentative (generatedMinimalCubicRepresentativeTable intervalOf) (generatedMinimalCubicRepresentativeTable_covers intervalOf)) ∧ RatInterval.CaseTable.Sound (generatedMinimalCubicRepresentativeTable intervalOf) (classifyBoundedLocalCoordinateByCubicRepresentative (generatedMinimalCubicRepresentativeTable intervalOf) (generatedMinimalCubicRepresentativeTable_covers intervalOf)) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.minimalRepTable_covers_and_sound_boundedLocal_of_cubicInvariant intervalOf value caseValue hvalue hinv hcase

/--
[classifyByMinimalCubicStableKey_eq_of_equivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma classifyByMinimalCubicStableKey_eq_of_equivalent_eq
  {d R maxDegree maxRange : ℕ}
  {c c' : BoundedPolymerCase d R maxDegree maxRange}
-- given
  (h : cubicEquivalent c c') :
-- imply
  classifyByMinimalCubicStableKey c = classifyByMinimalCubicStableKey c' := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.classifyByMinimalCubicStableKey_eq_of_equivalent h

/--
[classifyByMinimalCubicStableKey_ofLocalCoordinate_cubicTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma classifyByMinimalCubicStableKey_ofLocalCoordinate_cubicTransform_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R)
  (hbox' : (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  classifyByMinimalCubicStableKey (ofLocalCoordinate c hbox hdegree hrange) = classifyByMinimalCubicStableKey (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε) hbox' (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.classifyByMinimalCubicStableKey_ofLocalCoordinate_cubicTransform c v σ ε hbox hbox' hdegree hrange

/--
[classifyByMinimalCubicStableKey_ofLocalCoordinate_permute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma classifyByMinimalCubicStableKey_ofLocalCoordinate_permute_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {σ : Equiv.Perm (Fin d)}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  classifyByMinimalCubicStableKey (ofLocalCoordinate c hbox hdegree hrange) = classifyByMinimalCubicStableKey (ofLocalCoordinate (permuteLocalCoordinate c σ) (permuteLocalCoordinate_containedInBox c σ hbox) (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.classifyByMinimalCubicStableKey_ofLocalCoordinate_permute c σ hbox hdegree hrange

/--
[classifyByMinimalCubicStableKey_ofLocalCoordinate_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma classifyByMinimalCubicStableKey_ofLocalCoordinate_reflect_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  classifyByMinimalCubicStableKey (ofLocalCoordinate c hbox hdegree hrange) = classifyByMinimalCubicStableKey (ofLocalCoordinate (reflectLocalCoordinate c ε) (reflectLocalCoordinate_containedInBox c ε hbox) (by simpa using hdegree) (by simpa using hrange)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.classifyByMinimalCubicStableKey_ofLocalCoordinate_reflect c ε hbox hdegree hrange

/--
[generatedMinimalCubicStableKeyTable_covers_boundedCase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyTable_covers_boundedCase_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval} :
-- imply
  RatInterval.CaseTable.Covers (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf) (@classifyByMinimalCubicStableKey d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedMinimalCubicStableKeyTable_covers_boundedCase intervalOf

/--
[generatedMinimalCubicStableKeyTable_covers_diameterLocalCoordinate_after_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyTable_covers_diameterLocalCoordinate_after_translate_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {c : LocalPolymerCoordinate d}
-- given
  (hne : c.support.carrier.Nonempty)
  (hdiam : c.support.coordinateDiameterBound R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange), classifyByMinimalCubicStableKey bc ∈ (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf).cases ∧ ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧ bc.toPolymerSupport = c.support.translate v := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedMinimalCubicStableKeyTable_covers_diameterLocalCoordinate_after_translate intervalOf c hne hdiam hdegree hrange

/--
[generatedMinimalCubicStableKeyTable_sound_boundedCase_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyTable_sound_boundedCase_of_keyValue_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, caseValue c = keyValue (classifyByMinimalCubicStableKey c))
  (hkey : ∀ k, k ∈ (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf).cases → (intervalOf k).MemR (keyValue k)) :
-- imply
  RatInterval.CaseTable.Sound (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf) (@classifyByMinimalCubicStableKey d R maxDegree maxRange) caseValue := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedMinimalCubicStableKeyTable_sound_boundedCase_of_keyValue intervalOf caseValue keyValue hvalue hkey

/--
[minimalCubicStableKeyTable_covers_and_sound_boundedLocal_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma minimalCubicStableKeyTable_covers_and_sound_boundedLocal_of_keyValue_eq
  {d R maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, value c = keyValue (classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)))
  (hkey : ∀ k, k ∈ (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf).cases → (intervalOf k).MemR (keyValue k)) :
-- imply
  RatInterval.CaseTable.Covers (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) ∧ RatInterval.CaseTable.Sound (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.minimalCubicStableKeyTable_covers_and_sound_boundedLocal_of_keyValue intervalOf value keyValue hvalue hkey

/--
[coarseIntervalTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coarseIntervalTable_covers_eq
  {d R maxDegree maxRange : ℕ} :
-- imply
  RatInterval.CaseTable.Covers (coarseIntervalTable d R maxDegree maxRange) id := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.coarseIntervalTable_covers d R maxDegree maxRange

/--
[coarseIntervalTable_sound_of_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean)
-/
@[path]
private lemma coarseIntervalTable_sound_of_abs_le_one_eq
  {d R maxDegree maxRange : ℕ}
  {value : BoundedPolymerCase d R maxDegree maxRange → ℝ}
-- given
  (hvalue : ∀ c, |value c| ≤ 1) :
-- imply
  RatInterval.CaseTable.Sound (coarseIntervalTable d R maxDegree maxRange) id value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.coarseIntervalTable_sound_of_abs_le_one value hvalue


-- created on 2026-10-23
