import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexContourFull
open StatMech StatMech.Universality


/--
[hxc_hexOmega_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_hexOmega_ne_zero_eq :
-- imply
  hexOmega ≠ 0 := by
-- proof
  apply StatMech.Universality.hxc_hexOmega_ne_zero

/--
[hxc_paraf_support_subset_combined_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_paraf_support_subset_combined_p_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
-- given
  (hdu : du ≠ 0) :
-- imply
  Function.support (fun ts => parafSummand R.inRegion a h0 (v + du) (5/8) hexChi ts) ⊆ Function.support (combinedSummand R.inRegion a h0 v du) := by
-- proof
  apply StatMech.Universality.hxc_paraf_support_subset_combined_p R hdu

/--
[hxc_paraf_support_subset_combined_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_paraf_support_subset_combined_q_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
-- given
  (hdu : du ≠ 0) :
-- imply
  Function.support (fun ts => parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts) ⊆ Function.support (combinedSummand R.inRegion a h0 v du) := by
-- proof
  apply StatMech.Universality.hxc_paraf_support_subset_combined_q R hdu

/--
[hxc_paraf_support_subset_combined_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_paraf_support_subset_combined_r_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
-- given
  (hdu : du ≠ 0) :
-- imply
  Function.support (fun ts => parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) ⊆ Function.support (combinedSummand R.inRegion a h0 v du) := by
-- proof
  apply StatMech.Universality.hxc_paraf_support_subset_combined_r R hdu

/--
[hxc_paraf_summable_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_paraf_summable_p_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
-- given
  (hdu : du ≠ 0) :
-- imply
  Summable fun ts => parafSummand R.inRegion a h0 (v + du) (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.hxc_paraf_summable_p R hdu

/--
[hxc_paraf_summable_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_paraf_summable_q_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
-- given
  (hdu : du ≠ 0) :
-- imply
  Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.hxc_paraf_summable_q R hdu

/--
[hxc_paraf_summable_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_paraf_summable_r_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
-- given
  (hdu : du ≠ 0) :
-- imply
  Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.hxc_paraf_summable_r R hdu

/--
[hxc_combinedSummand_tsum_eq_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_combinedSummand_tsum_eq_finset_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
-- given
  (hdu : du ≠ 0) :
-- imply
  ∑' ts, combinedSummand R.inRegion a h0 v du ts = ∑ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, combinedSummand R.inRegion a h0 v du ts := by
-- proof
  apply StatMech.Universality.hxc_combinedSummand_tsum_eq_finset R hdu

/--
[hxc_vertexSum_eq_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_vertexSum_eq_finset_sum_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
-- given
  (hdu : du ≠ 0) :
-- imply
  ((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = ∑ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, combinedSummand R.inRegion a h0 v du ts := by
-- proof
  apply StatMech.Universality.hxc_vertexSum_eq_finset_sum R hdu

/--
[hxc_vertex_relation_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_vertex_relation_finite_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {C : HexSawClassification R.inRegion a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hxc_vertex_relation_finite R C hdu

/--
[hxc_finset_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_finset_sum_eq_zero_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {C : HexSawClassification R.inRegion a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ∑ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, combinedSummand R.inRegion a h0 v du ts = 0 := by
-- proof
  apply StatMech.Universality.hxc_finset_sum_eq_zero R C hdu

/--
[hxc_paraf_support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_paraf_support_finite_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {z : ℂ}
  {σ x : ℝ} :
-- imply
  (Function.support (fun ts => parafSummand R.inRegion a h0 z σ x ts)).Finite := by
-- proof
  apply StatMech.Universality.hxc_paraf_support_finite R z σ x

/--
[hxc_paraf_observable_eq_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_paraf_observable_eq_finset_sum_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {z : ℂ}
  {σ x : ℝ} :
-- imply
  parafObservable R.inRegion a h0 z σ x = ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) z σ x).toFinset, parafSummand R.inRegion a h0 z σ x ts := by
-- proof
  apply StatMech.Universality.hxc_paraf_observable_eq_finset_sum R z σ x

/--
[hxc_familyFSum_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_familyFSum_finite_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  [DecidableEq V]
  {R : HexFiniteRegion}
  {D : HexDomain V}
  {s : HexSide D}
-- given
  (hObs : ∀ z, D.obs z = parafObservable R.inRegion a h0 z (5/8) hexChi) :
-- imply
  s.fSum = ∑ e ∈ s.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.hxc_familyFSum_finite R D s hObs

/--
[hxc_boundarySum_assignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_boundarySum_assignment_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  [DecidableEq V]
  {R : HexFiniteRegion}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexBoundaryDecomp D P}
-- given
  (hObs : ∀ z, D.obs z = parafObservable R.inRegion a h0 z (5/8) hexChi) :
-- imply
  D.boundarySum P = B.A.dir * (∑ e ∈ B.A.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) + B.L.dir * (∑ e ∈ B.L.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) + B.Tp.dir * (∑ e ∈ B.Tp.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) + B.Tm.dir * (∑ e ∈ B.Tm.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) + B.U.dir * (∑ e ∈ B.U.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) := by
-- proof
  apply StatMech.Universality.hxc_boundarySum_assignment R D P B hObs

/--
[hxc_finite_enum_eq_contour_proj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_finite_enum_eq_contour_proj_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  [DecidableEq V]
  {R : HexFiniteRegion}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexBoundaryDecomp D P}
-- given
  (hObs : ∀ z, D.obs z = parafObservable R.inRegion a h0 z (5/8) hexChi) :
-- imply
  B.A.dir * (∑ e ∈ B.A.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) + B.L.dir * (∑ e ∈ B.L.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) + B.Tp.dir * (∑ e ∈ B.Tp.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) + B.Tm.dir * (∑ e ∈ B.Tm.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) + B.U.dir * (∑ e ∈ B.U.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) (D.mid e.vtx e.edge) (5/8) hexChi).toFinset, parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) = Complex.I * (((hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups : ℝ) - (B.Fa : ℝ)) : ℂ) := by
-- proof
  apply StatMech.Universality.hxc_finite_enum_eq_contour_proj R D P B hObs

/--
[hxc_boundary_identity_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourFull.lean)
-/
@[path]
private lemma hxc_boundary_identity_finite_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  [DecidableEq V]
  {R : HexFiniteRegion}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexBoundaryDecomp D P}
-- given
  (hsub : P.interior ⊆ D.incidences)
  (hObs : ∀ z, D.obs z = parafObservable R.inRegion a h0 z (5/8) hexChi)
  (hFa : B.Fa = 1) :
-- imply
  hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups = 1 := by
-- proof
  apply StatMech.Universality.hxc_boundary_identity_finite R D P hsub B hObs hFa


-- created on 2026-10-23
