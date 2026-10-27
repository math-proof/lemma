import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
open SimpleGraph Function StatMech StatMech.Lattice


/--
[facingDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma facingDart_head_eq
  {v g : Site 2}
-- given
  (hg : unitWt g = 1) :
-- imply
  (facingDart v g hg).head = v := by
-- proof
  apply StatMech.Lattice.facingDart_head v g hg

/--
[facingDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma facingDart_dir_eq
  {v g : Site 2}
-- given
  (hg : unitWt g = 1) :
-- imply
  (facingDart v g hg).dir = g := by
-- proof
  apply StatMech.Lattice.facingDart_dir v g hg

/--
[facingDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma facingDart_tail_eq
  {v g : Site 2}
-- given
  (hg : unitWt g = 1) :
-- imply
  (facingDart v g hg).tail = v - g := by
-- proof
  apply StatMech.Lattice.facingDart_tail v g hg

/--
[facingDart_isBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma facingDart_isBoundary_eq
  {K : Set (Site 2)}
  {v g : Site 2}
-- given
  (hg : unitWt g = 1)
  (htail : v - g ∈ K)
  (hv : v ∉ K) :
-- imply
  IsBoundaryDart K (facingDart v g hg) := by
-- proof
  apply StatMech.Lattice.facingDart_isBoundary K v g hg htail hv

/--
[ifc_arc_to_innerCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_arc_to_innerCorner_eq
  {K : Set (Site 2)}
  {d : Dart}
  {v : Site 2}
-- given
  (hv : d.head = v) :
-- imply
  ∀ k : ℕ, (∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K) → (∀ j < k, IsInnerCorner K ((dartNext K)^[j] d)) := by
-- proof
  apply StatMech.Lattice.ifc_arc_to_innerCorner K d v hv

/--
[ifc_facing_rotateArc_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_facing_rotateArc_sameOrbit_eq
  {K : Set (Site 2)}
  {e d : Dart}
  {v : Site 2}
  {k : ℕ}
-- given
  (hd : IsBoundaryDart K d)
  (hv : d.head = v)
  (hsame : SameOrbit K e d)
  (harc : ∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K) :
-- imply
  ∃ d' : Dart, IsBoundaryDart K d' ∧ d'.head = v ∧ d'.dir = rot90Fun^[k] d.dir ∧ SameOrbit K e d' := by
-- proof
  apply StatMech.Lattice.ifc_facing_rotateArc_sameOrbit K e d hd v hv hsame k harc

/--
[ifc_orbitVertexSaturate_contiguous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_orbitVertexSaturate_contiguous_eq
  {K : Set (Site 2)}
  {e d : Dart}
  {v : Site 2}
  {k : ℕ}
  {d' : Dart}
-- given
  (hd : IsBoundaryDart K d)
  (hv : d.head = v)
  (hsame : SameOrbit K e d)
  (harc : ∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K)
  (_hd' : IsBoundaryDart K d')
  (hv' : d'.head = v)
  (hdir' : d'.dir = rot90Fun^[k] d.dir) :
-- imply
  SameOrbit K e d' := by
-- proof
  apply StatMech.Lattice.ifc_orbitVertexSaturate_contiguous K e d hd v hv hsame k harc d' _hd' hv' hdir'

/--
[ifc_dartNext_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_dartNext_singleton_eq
  {c : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
-- imply
  (dartNext ({c} : Set (Site 2)) e).tail = c ∧ (dartNext ({c} : Set (Site 2)) e).dir = -rot90Fun e.dir := by
-- proof
  apply StatMech.Lattice.ifc_dartNext_singleton c e he

/--
[ifc_dartNext_singleton_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_dartNext_singleton_iterate_eq
  {c : Site 2}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
-- imply
  ((dartNext ({c} : Set (Site 2)))^[n] e).tail = c ∧ ((dartNext ({c} : Set (Site 2)))^[n] e).dir = (fun x => -rot90Fun x)^[n] e.dir := by
-- proof
  apply StatMech.Lattice.ifc_dartNext_singleton_iterate c e he n

/--
[ifc_unit_four_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_unit_four_cases_eq
  {g : Site 2}
-- given
  (hg : unitWt g = 1) :
-- imply
  g = ![1, 0] ∨ g = ![-1, 0] ∨ g = ![0, 1] ∨ g = ![0, -1] := by
-- proof
  apply StatMech.Lattice.ifc_unit_four_cases g hg

/--
[ifc_singleton_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_singleton_cover_eq
  {g0 g1 : Site 2}
-- given
  (h0 : unitWt g0 = 1)
  (h1 : unitWt g1 = 1) :
-- imply
  ∃ n : ℕ, (fun x => -rot90Fun x)^[n] g0 = g1 := by
-- proof
  apply StatMech.Lattice.ifc_singleton_cover g0 g1 h0 h1

/--
[ifc_singleton_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_singleton_sameOrbit_eq
  {c : Site 2}
  {e f : Dart}
-- given
  (he : IsBoundaryDart ({c} : Set (Site 2)) e)
  (hf : IsBoundaryDart ({c} : Set (Site 2)) f) :
-- imply
  SameOrbit ({c} : Set (Site 2)) e f := by
-- proof
  apply StatMech.Lattice.ifc_singleton_sameOrbit c e f he hf

/--
[ifc_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean)
-/
@[path]
private lemma ifc_interfaceConnected_eq
  {c : Site 2} :
-- imply
  InterfaceConnected ({c} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.ifc_interfaceConnected c


-- created on 2026-10-23
