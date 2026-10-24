import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexBrickWiredCofinal
open Filter Finset MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[monotone_triangularBoxActiveRestrictLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma monotone_triangularBoxActiveRestrictLE_eq
  {n m : Nat}
-- given
  (hnm : n ≤ m) :
-- imply
  Monotone (triangularBoxActiveRestrictLE hnm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.monotone_triangularBoxActiveRestrictLE hnm

/--
[triHexFaceDualInnerActive_restrictLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triHexFaceDualInnerActive_restrictLE_eq
  {n m : Nat}
  {omega : ConfigSpace (Sym2 HexVertex)}
-- given
  (hnm : n ≤ m) :
-- imply
  triangularBoxActiveRestrictLE hnm (triHexFaceDualInnerActive m omega) = triHexFaceDualInnerActive n omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFaceDualInnerActive_restrictLE hnm omega

/--
[triangularBoxLiftEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBoxLiftEvent_increasing_eq
  {n m : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph n).edgeSet)}
-- given
  (hnm : n ≤ m)
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (triangularBoxLiftEvent hnm A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxLiftEvent_increasing hnm hA

/--
[triHexFaceDualInnerEvent_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triHexFaceDualInnerEvent_lift_eq
  {n m : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph n).edgeSet)}
-- given
  (hnm : n ≤ m) :
-- imply
  triHexFaceDualInnerEvent m (triangularBoxLiftEvent hnm A) = triHexFaceDualInnerEvent n A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFaceDualInnerEvent_lift hnm A

/--
[monotone_triangularBoxBufferedActiveRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma monotone_triangularBoxBufferedActiveRestrict_eq
  {k m : Nat}
-- given
  (hkm : 2 * k ≤ triangular.bufferedRadius m) :
-- imply
  Monotone (triangularBoxBufferedActiveRestrict k m hkm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.monotone_triangularBoxBufferedActiveRestrict k m hkm

/--
[triangularBufferedBoxActiveEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBufferedBoxActiveEvent_increasing_eq
  {k m : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
-- given
  (hkm : 2 * k ≤ triangular.bufferedRadius m)
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (triangularBufferedBoxActiveEvent k m hkm A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedBoxActiveEvent_increasing k m hkm hA

/--
[triangularBufferedBoxEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBufferedBoxEvent_increasing_eq
  {k : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (triangularBufferedBoxEvent k A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedBoxEvent_increasing k hA

/--
[triangularBoxBufferedActiveRestrict_bufferedRestrictLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBoxBufferedActiveRestrict_bufferedRestrictLE_eq
  {k m : Nat}
  {rho : ConfigSpace (Sym2 (triangular.BufferedVertex m))}
-- given
  (hkm : 2 * k ≤ m) :
-- imply
  triangularBoxBufferedActiveRestrict k (2 * k) (triangular.id_le_bufferedRadius (2 * k)) (restrictActive (triangular.bufferedGraph (2 * k)) (triangular.bufferedRestrictLE hkm rho)) = triangularBoxBufferedActiveRestrict k m ((triangular.id_le_bufferedRadius (2 * k)).trans (triangular.bufferedRadius_strictMono.monotone hkm)) (restrictActive (triangular.bufferedGraph m) rho) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxBufferedActiveRestrict_bufferedRestrictLE k m hkm rho

/--
[triangularBufferedBoxEvent_preimage_restrictActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBufferedBoxEvent_preimage_restrictActive_eq
  {k m : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
-- given
  (hkm : 2 * k ≤ m) :
-- imply
  triangular.bufferedRestrictLE hkm ⁻¹' triangularBufferedBoxEvent k A = restrictActive (triangular.bufferedGraph m) ⁻¹' triangularBufferedBoxActiveEvent k m ((triangular.id_le_bufferedRadius (2 * k)).trans (triangular.bufferedRadius_strictMono.monotone hkm)) A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedBoxEvent_preimage_restrictActive k m hkm A

/--
[triangularBufferedBoxEvent_centeredShell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBufferedBoxEvent_centeredShell_eq_eq
  {k : Nat} :
-- imply
  triangularBufferedBoxEvent k (triangularCenteredShellEvent (2 * k) k) = triangularBufferedInnerShellEvent k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedBoxEvent_centeredShell_eq k

/--
[triangularBoxRead_dualConfig_eq_triHexFaceDualInnerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBoxRead_dualConfig_eq_triHexFaceDualInnerActive_eq
  {k : Nat}
  {omega : ConfigSpace (Sym2 HexVertex)} :
-- imply
  triangularBoxBufferedActiveRestrict k (2 * k) (triangular.id_le_bufferedRadius (2 * k)) (restrictActive (triangular.bufferedGraph (2 * k)) (triangular.bufferedRestrict (2 * k) ((dualConfigEquiv triHexFullDualEdgeEquiv).symm omega))) = triHexFaceDualInnerActive (2 * k) omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxRead_dualConfig_eq_triHexFaceDualInnerActive k omega

/--
[triHexFaceDualInnerShell_eq_dualConfig_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triHexFaceDualInnerShell_eq_dualConfig_preimage_eq
  {k : Nat} :
-- imply
  triHexFaceDualInnerEvent (2 * k) (triangularCenteredShellEvent (2 * k) k) = (dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹' triangular.bufferedCylinder (2 * k) (triangularBufferedInnerShellEvent k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFaceDualInnerShell_eq_dualConfig_preimage k

/--
[triHex_dualPercolationEvent_subset_faceDualInnerShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triHex_dualPercolationEvent_subset_faceDualInnerShell_eq
  {k : Nat}
-- given
  (hk : 1 ≤ k) :
-- imply
  (dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹' triangular.percolationEvent ⊆ triHexFaceDualInnerEvent (2 * k) (triangularCenteredShellEvent (2 * k) k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHex_dualPercolationEvent_subset_faceDualInnerShell k hk

/--
[triangularBufferedInnerShellCylinder_subset_rootBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBufferedInnerShellCylinder_subset_rootBoundary_eq
  {k n : Nat}
-- given
  (hnk : triangular.bufferedRadius n < k) :
-- imply
  triangular.bufferedCylinder (2 * k) (triangularBufferedInnerShellEvent k) ⊆ triangular.bufferedCylinder n (triangular.bufferedRootBoundaryEvent n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedInnerShellCylinder_subset_rootBoundary k n hnk

/--
[triangularBoxBufferedActiveRestrict_comp_outerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularBoxBufferedActiveRestrict_comp_outerBox_eq
  {k j M : Nat}
  {rho : ConfigSpace (triangularBoxGraph (2 * M)).edgeSet}
-- given
  (hkj : 2 * k ≤ triangular.bufferedRadius j)
  (hjM : triangular.bufferedRadius j ≤ 2 * M) :
-- imply
  triangularBoxBufferedActiveRestrict k j hkj (ocd_innerRestrictActive (triangular.bufferedGraph j) (triangularBoxGraph (2 * M)) (triangularBufferedToBox j M hjM) (triangularBufferedToBox_adjMatch j M hjM) rho) = triangularBoxActiveRestrictLE (hkj.trans hjM) rho := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxBufferedActiveRestrict_comp_outerBox k j M hkj hjM rho

/--
[hexagonalFreeInfinite_faceDual_le_triangularWiredBuffered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma hexagonalFreeInfinite_faceDual_le_triangularWiredBuffered_eq
  {k j : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
-- given
  (hkj : 2 * k ≤ j)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent (2 * k) A) ≤ (triangular.wiredBufferedMeasure j (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * k) (triangularBufferedBoxEvent k A)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFreeInfinite_faceDual_le_triangularWiredBuffered k j hkj hp hp1 hq hA

/--
[triangularFreeBufferedBox_le_hexagonalFreeInfinite_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularFreeBufferedBox_le_hexagonalFreeInfinite_faceDual_eq
  {k j : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
-- given
  (hkj : 2 * k ≤ j)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (triangular.freeBufferedMeasure j (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * k) (triangularBufferedBoxEvent k A)) ≤ (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent (2 * k) A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularFreeBufferedBox_le_hexagonalFreeInfinite_faceDual k j hkj hp hp1 hq hA

/--
[triangularFreeInfinite_le_hexagonalFreeInfinite_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularFreeInfinite_le_hexagonalFreeInfinite_faceDual_eq
  {k : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (triangular.freeBufferedInfiniteVolume (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * k) (triangularBufferedBoxEvent k A)) ≤ (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent (2 * k) A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularFreeInfinite_le_hexagonalFreeInfinite_faceDual k hp hp1 hq hA

/--
[hexagonalFreeInfinite_faceDual_le_triangularWiredInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma hexagonalFreeInfinite_faceDual_le_triangularWiredInfinite_eq
  {k : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent (2 * k) A) ≤ (triangular.wiredBufferedInfiniteVolume (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * k) (triangularBufferedBoxEvent k A)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFreeInfinite_faceDual_le_triangularWiredInfinite k hp hp1 hq hA

/--
[triangularFree_hexagonalFaceDual_triangularWired_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularFree_hexagonalFaceDual_triangularWired_sandwich_eq
  {k : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (triangular.freeBufferedInfiniteVolume (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * k) (triangularBufferedBoxEvent k A)) ≤ (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent (2 * k) A) ∧ (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent (2 * k) A) ≤ (triangular.wiredBufferedInfiniteVolume (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * k) (triangularBufferedBoxEvent k A)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularFree_hexagonalFaceDual_triangularWired_sandwich k hp hp1 hq hA

/--
[hexagonalFreeInfinite_faceDual_finiteEvent_le_triangularWiredInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma hexagonalFreeInfinite_faceDual_finiteEvent_le_triangularWiredInfinite_eq
  {N : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent N A) ≤ (triangular.wiredBufferedInfiniteVolume (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * N) (triangularBufferedBoxEvent N (triangularBoxLiftEvent (by omega : N ≤ 2 * N) A))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFreeInfinite_faceDual_finiteEvent_le_triangularWiredInfinite N hp hp1 hq hA

/--
[hexagonalFreeInfinite_dualPercolation_le_triangularWiredPercolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma hexagonalFreeInfinite_dualPercolation_le_triangularWiredPercolation_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹' triangular.percolationEvent) ≤ triangular.wiredPercolationProbability (dualParam p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFreeInfinite_dualPercolation_le_triangularWiredPercolation hp hp1 hq

/--
[triangularFreePercolation_le_hexagonalFreeDualPercolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularFreePercolation_le_hexagonalFreeDualPercolation_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (triangular.freeBufferedInfiniteVolume (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real triangular.percolationEvent ≤ (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹' triangular.percolationEvent) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularFreePercolation_le_hexagonalFreeDualPercolation hp hp1 hq

/--
[triangularFree_hexagonalFreeDual_triangularWired_percolation_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularFree_hexagonalFreeDual_triangularWired_percolation_sandwich_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (triangular.freeBufferedInfiniteVolume (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real triangular.percolationEvent ≤ (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹' triangular.percolationEvent) ∧ (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹' triangular.percolationEvent) ≤ triangular.wiredPercolationProbability (dualParam p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularFree_hexagonalFreeDual_triangularWired_percolation_sandwich hp hp1 hq

/--
[hexagonalFreeDualPercolation_pos_of_triangularFreePercolation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma hexagonalFreeDualPercolation_pos_of_triangularFreePercolation_pos_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htri : 0 < (triangular.freeBufferedInfiniteVolume (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real triangular.percolationEvent) :
-- imply
  0 < (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹' triangular.percolationEvent) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFreeDualPercolation_pos_of_triangularFreePercolation_pos hp hp1 hq htri

/--
[triangularWiredPercolates_dualParam_of_hexagonalFreeDualPercolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean)
-/
@[path]
private lemma triangularWiredPercolates_dualParam_of_hexagonalFreeDualPercolation_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hdual : 0 < (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹' triangular.percolationEvent)) :
-- imply
  triangular.wiredPercolates (dualParam p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularWiredPercolates_dualParam_of_hexagonalFreeDualPercolation hp hp1 hq hdual


-- created on 2026-10-23
