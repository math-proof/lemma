/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.BetweenList
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Side
import Mathlib.RingTheory.Valuation.LocalSubring
import Theorem.MeasureTheory.Measure.Lebesgue.TriangleArea.Part3
import Lemma.Measure.Lebesgue.TriangleArea
import Def.Geometry.Dissections.Monsky.Part8
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma monsky_exists_atom_probes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) :
    ∃ p n : EuclideanSpace ℝ (Fin 2),
      (∀ g : MonskyFace T,
        monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
              monskyFaceForm T htriangle hcard hvolume g p ∧
            0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
              monskyFaceForm T htriangle hcard hvolume g n) ∧
      (∀ g : MonskyFace T,
        monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
          monskyFaceForm T htriangle hcard hvolume g p *
            monskyFaceForm T htriangle hcard hvolume g n < 0) := by
  let m := monskyAtomMidpoint e
  let z := monskyFaceOffPoint T htriangle f
  let probe : ℝ → EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap m z
  have hevent : ∀ᶠ r in nhds (0 : ℝ), ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g m ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g m *
            monskyFaceForm T htriangle hcard hvolume g (probe r) ∧
          0 < monskyFaceForm T htriangle hcard hvolume g m *
            monskyFaceForm T htriangle hcard hvolume g (probe (-r)) := by
    rw [Filter.eventually_all]
    intro g
    by_cases hzero : monskyFaceForm T htriangle hcard hvolume g m = 0
    · exact Filter.Eventually.of_forall fun _ hne ↦ (hne hzero).elim
    · let F := monskyFaceForm T htriangle hcard hvolume g
      have hFcont := monsky_faceForm_continuous T htriangle hcard hvolume g
      have hprobeCont : Continuous probe := AffineMap.lineMap_continuous
      have hnegProbeCont : Continuous (fun r ↦ probe (-r)) :=
        hprobeCont.comp continuous_neg
      have hplusCont : Continuous (fun r ↦ F m * F (probe r)) :=
        continuous_const.mul (hFcont.comp hprobeCont)
      have hminusCont : Continuous (fun r ↦ F m * F (probe (-r))) :=
        continuous_const.mul (hFcont.comp hnegProbeCont)
      have hsquare : 0 < F m * F m := mul_self_pos.mpr hzero
      have hplus0 : 0 < F m * F (probe 0) := by
        simpa [probe] using hsquare
      have hminus0 : 0 < F m * F (probe (-0)) := by
        simpa [probe] using hsquare
      filter_upwards [continuousAt_const.eventually_lt hplusCont.continuousAt hplus0,
        continuousAt_const.eventually_lt hminusCont.continuousAt hminus0] with r hp hn
      exact fun _ ↦ ⟨hp, hn⟩
  obtain ⟨ε, hε, hpreserve⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδdist : dist δ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    dsimp [δ]
    linarith
  have hpreserveδ := hpreserve hδdist
  refine ⟨probe δ, probe (-δ), ?_, ?_⟩
  · simpa only [m] using hpreserveδ
  · intro g hgm
    have hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g :=
      (monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume g (monskyAtomMidpoint e)).2 hgm
    have hline : monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
      by_contra hne
      exact monsky_atomMidpoint_not_mem_distinct_faceLine
        T htriangle hcard hvolume f g e hef hne hmg
    have hznotf : z ∉ monskyFaceLine T htriangle f := by
      intro hzf
      have hz0 := (monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume f z).1 hzf
      exact (ne_of_gt (monsky_faceForm_offPoint_pos
        T htriangle hcard hvolume f)) hz0
    have hznotg : z ∉ monskyFaceLine T htriangle g := by
      rwa [← hline]
    have hgz : monskyFaceForm T htriangle hcard hvolume g z ≠ 0 := by
      intro hzero
      exact hznotg ((monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume g z).2 hzero)
    have hplus : monskyFaceForm T htriangle hcard hvolume g (probe δ) =
        AffineMap.lineMap
          (monskyFaceForm T htriangle hcard hvolume g m)
          (monskyFaceForm T htriangle hcard hvolume g z) δ := by
      exact (monskyFaceForm T htriangle hcard hvolume g).apply_lineMap m z δ
    have hminus : monskyFaceForm T htriangle hcard hvolume g (probe (-δ)) =
        AffineMap.lineMap
          (monskyFaceForm T htriangle hcard hvolume g m)
          (monskyFaceForm T htriangle hcard hvolume g z) (-δ) := by
      exact (monskyFaceForm T htriangle hcard hvolume g).apply_lineMap m z (-δ)
    rw [hplus, hminus]
    have hgm' : monskyFaceForm T htriangle hcard hvolume g m = 0 := by
      simpa only [m] using hgm
    rw [hgm']
    change AffineMap.lineMap 0
        (monskyFaceForm T htriangle hcard hvolume g z) δ *
      AffineMap.lineMap 0
        (monskyFaceForm T htriangle hcard hvolume g z) (-δ) < 0
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
      sub_zero]
    have hprod : δ * monskyFaceForm T htriangle hcard hvolume g z ≠ 0 :=
      mul_ne_zero hδ.ne' hgz
    nlinarith [mul_self_pos.mpr hprod]

end MetaMathlibExt
