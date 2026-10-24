import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexVertexFull
open StatMech StatMech.Universality StatMech.Universality.HexFiniteRegion


/--
[hxv_mem_supportVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_mem_supportVertices_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {x : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  x ∈ R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu ↔ ∃ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), x ∈ (ofTurns a h0 ts).vertices := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hxv_mem_supportVertices R hdu x

/--
[hxv_support_vertexBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_support_vertexBound_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hts : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
-- imply
  ∀ x ∈ (ofTurns a h0 ts).vertices, x ∈ R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hxv_support_vertexBound R hdu ts hts

/--
[hxv_supportVertices_subset_verts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_supportVertices_subset_verts_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu ⊆ R.verts := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hxv_supportVertices_subset_verts R hdu

/--
[hxv_supportVertices_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_supportVertices_finite_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  (R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu : Set ℂ).Finite := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hxv_supportVertices_finite R hdu

/--
[hxv_supportVertices_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_supportVertices_card_le_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  (R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu).card ≤ R.verts.card := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hxv_supportVertices_card_le R hdu

/--
[hxv_support_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_support_endsAt_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hts : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
-- imply
  (ofTurns a h0 ts).EndsAt (v + du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega * du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hxv_support_endsAt R ts hts

/--
[hxv_support_isLegalSAW_staysIn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_support_isLegalSAW_staysIn_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hts : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
-- imply
  (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn R.inRegion := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hxv_support_isLegalSAW_staysIn R hdu ts hts

/--
[hxv_full_vertexBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_full_vertexBound_eq
  {M : Finset ℂ}
  {a : ℂ}
  {w : HexWalk}
-- given
  (ha : a ∈ M)
  (hstay : ∀ m ∈ w.mids, m ∈ (hexStrip_finiteRegion M a ha).mids) :
-- imply
  ∀ x ∈ w.vertices, x ∈ (hexStrip_finiteRegion M a ha).verts := by
-- proof
  apply StatMech.Universality.hxv_full_vertexBound M a ha w hstay

/--
[hxv_singleRegion_support_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_singleRegion_support_empty_eq
  {a : ℂ} :
-- imply
  Function.support (combinedSummand (hexStrip_singleRegion a).inRegion a 0 a 1) = ∅ := by
-- proof
  apply StatMech.Universality.hxv_singleRegion_support_empty a

/--
[hxv_singleRegion_supportVertices_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_singleRegion_supportVertices_empty_eq
  {a : ℂ} :
-- imply
  (hexStrip_singleRegion a).hxv_supportVertices (a := a) (h0 := 0) (v := a) (du := 1) one_ne_zero = ∅ := by
-- proof
  apply StatMech.Universality.hxv_singleRegion_supportVertices_empty a

/--
[hxv_support_insufficient_for_allWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean)
-/
@[path]
private lemma hxv_support_insufficient_for_allWalks_eq
  {a : ℂ} :
-- imply
  ∃ (w : HexWalk) (x : ℂ), (∀ m ∈ w.mids, m ∈ (hexStrip_singleRegion a).mids) ∧ x ∈ w.vertices ∧ x ∉ (hexStrip_singleRegion a).hxv_supportVertices (a := a) (h0 := 0) (v := a) (du := 1) one_ne_zero := by
-- proof
  apply StatMech.Universality.hxv_support_insufficient_for_allWalks a


-- created on 2026-10-23
