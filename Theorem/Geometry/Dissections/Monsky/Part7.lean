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
import Def.Geometry.Dissections.Monsky.Part7
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma monsky_mem_faceParamList_bounds
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r : ℝ} (hr : r ∈ monskyFaceParamList T htriangle f) :
    0 ≤ r ∧ r ≤ 1 := by
  rw [monskyFaceParamList, List.mem_append] at hr
  rcases hr with hr | hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · norm_num
    · have hir := (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
        ((Finset.mem_sort _).1 hr)).1
      exact ⟨hir.1.le, hir.2.le⟩
  · have hr1 : r = 1 := List.mem_singleton.mp hr
    subst r
    norm_num

lemma monsky_atomMidpoint_mem_openSegment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (he : e ∈ monskyFaceAtomList T htriangle f) :
    monskyAtomMidpoint e ∈
      openSegment ℝ (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f) := by
  obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 he
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hr := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_fst_mem_of_mem_consecutivePairs hrq)
  have hq := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_snd_mem_of_mem_consecutivePairs hrq)
  rw [openSegment_eq_image_lineMap]
  refine ⟨midpoint ℝ r q, ?_, ?_⟩
  · simp only [midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    constructor <;> norm_num <;> linarith
  · exact (monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq).symm

lemma monsky_atomMidpoint_not_mem_distinct_faceLine
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f g : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (he : e ∈ monskyFaceAtomList T htriangle f)
    (hfg : monskyFaceLine T htriangle f ≠ monskyFaceLine T htriangle g) :
    monskyAtomMidpoint e ∉ monskyFaceLine T htriangle g := by
  intro hmg
  obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 he
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
  let u := midpoint ℝ r q
  have hm : monskyAtomMidpoint e = L u :=
    monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq
  have hmf : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle f := by
    rw [hm, monskyFaceLine]
    exact AffineMap.lineMap_mem_affineSpan_pair u _ _
  have hinter : monskyIntersectionPoint T htriangle f g = monskyAtomMidpoint e :=
    monsky_intersectionPoint_eq_of_mem T htriangle f g hfg hmf hmg
  have hmnode : monskyAtomMidpoint e ∈ monskyNodes T htriangle := by
    rw [← hinter]
    exact monsky_intersectionPoint_mem_nodes T htriangle f g
  have hmopen := monsky_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e he
  have huparam : u ∈ monskyFaceInteriorParams T htriangle f := by
    have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hmnode hmopen
    have hLinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hinvu : Function.invFun L (monskyAtomMidpoint e) = u := by
      rw [hm]
      exact Function.leftInverse_invFun hLinj u
    rwa [hinvu] at hinv
  have hulist : u ∈ monskyFaceParamList T htriangle f := by
    rw [monskyFaceParamList, List.mem_append]
    left
    exact List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 huparam)
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hubetween : r < u ∧ u < q := by
    simp only [u, midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    constructor <;> norm_num <;> linarith
  exact monsky_not_between_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq hulist hubetween

lemma monsky_lineMap_mem_nodes_of_mem_paramList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r : ℝ} (hr : r ∈ monskyFaceParamList T htriangle f) :
    AffineMap.lineMap (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f) r ∈ monskyNodes T htriangle := by
  rw [monskyFaceParamList, List.mem_append] at hr
  rcases hr with hr | hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · simpa using monsky_faceLeft_mem_nodes T htriangle f
    · exact (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
        ((Finset.mem_sort _).1 hr)).2
  · have hr1 : r = 1 := List.mem_singleton.mp hr
    subst r
    simpa using monsky_faceRight_mem_nodes T htriangle f

lemma monsky_mem_pointList_of_mem_nodes_of_mem_segment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {x : EuclideanSpace ℝ (Fin 2)}
    (hnode : x ∈ monskyNodes T htriangle)
    (hsegment : x ∈ segment ℝ (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f)) :
    x ∈ monskyFacePointList T htriangle f := by
  rw [segment_eq_image_lineMap] at hsegment
  obtain ⟨r, hr, hrx⟩ := hsegment
  have hparam : r ∈ monskyFaceParamList T htriangle f := by
    rcases eq_or_lt_of_le hr.1 with rfl | hr0
    · rw [monskyFaceParamList, List.mem_append]
      exact Or.inl (by simp)
    · rcases eq_or_lt_of_le hr.2 with rfl | hr1
      · rw [monskyFaceParamList, List.mem_append]
        exact Or.inr (by simp)
      · have hopen : x ∈ openSegment ℝ (monskyFaceLeft T htriangle f)
            (monskyFaceRight T htriangle f) := by
          rw [openSegment_eq_image_lineMap]
          exact ⟨r, ⟨hr0, hr1⟩, hrx⟩
        have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hnode hopen
        have hinj := AffineMap.lineMap_injective ℝ
          (monsky_face_endpoints_ne T htriangle hcard hvolume f)
        have hinvr : Function.invFun (AffineMap.lineMap
            (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)) x = r := by
          rw [← hrx]
          exact Function.leftInverse_invFun hinj r
        rw [hinvr] at hinv
        rw [monskyFaceParamList, List.mem_append]
        exact Or.inl (List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 hinv))
  rw [monskyFacePointList, List.mem_map]
  exact ⟨r, hparam, hrx⟩

lemma monsky_no_node_mem_openSegment_of_consecutive
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r q : ℝ}
    (hrq : (r, q) ∈ (monskyFaceParamList T htriangle f).consecutivePairs)
    {x : EuclideanSpace ℝ (Fin 2)} (hnode : x ∈ monskyNodes T htriangle) :
    x ∉ openSegment ℝ
      (AffineMap.lineMap (monskyFaceLeft T htriangle f)
        (monskyFaceRight T htriangle f) r)
      (AffineMap.lineMap (monskyFaceLeft T htriangle f)
        (monskyFaceRight T htriangle f) q) := by
  intro hxopen
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
  rw [openSegment_eq_image_lineMap] at hxopen
  obtain ⟨t, ht, htx⟩ := hxopen
  let u := AffineMap.lineMap r q t
  have hLux : L u = x := by
    change L (AffineMap.lineMap r q t) = x
    rw [L.apply_lineMap, htx]
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hubetween : r < u ∧ u < q := by
    simp only [u, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    constructor <;> nlinarith [ht.1, ht.2]
  have hrbounds := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_fst_mem_of_mem_consecutivePairs hrq)
  have hqbounds := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_snd_mem_of_mem_consecutivePairs hrq)
  have huopen : x ∈ openSegment ℝ (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f) := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨u, ⟨hrbounds.1.trans_lt hubetween.1,
      hubetween.2.trans_le hqbounds.2⟩, hLux⟩
  have huparam : u ∈ monskyFaceInteriorParams T htriangle f := by
    have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hnode huopen
    have hinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hinvu : Function.invFun L x = u := by
      rw [← hLux]
      exact Function.leftInverse_invFun hinj u
    rwa [hinvu] at hinv
  have hulist : u ∈ monskyFaceParamList T htriangle f := by
    rw [monskyFaceParamList, List.mem_append]
    exact Or.inl (List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 huparam))
  exact monsky_not_between_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq hulist hubetween

lemma monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (g : MonskyFace T) :
    e ∈ monskyFaceAtomList T htriangle g ↔
      monskyAtomMidpoint e ∈
        openSegment ℝ (monskyFaceLeft T htriangle g) (monskyFaceRight T htriangle g) := by
  constructor
  · exact monsky_atomMidpoint_mem_openSegment T htriangle hcard hvolume g e
  · intro hmopen
    obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 hef
    let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
    let G : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (monskyFaceLeft T htriangle g) (monskyFaceRight T htriangle g)
    have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
      (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
    have hm : monskyAtomMidpoint e = L (midpoint ℝ r q) :=
      monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq
    rw [openSegment_eq_image_lineMap] at hmopen
    obtain ⟨t, ht, htm⟩ := hmopen
    have hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g := by
      rw [← htm, monskyFaceLine]
      exact AffineMap.lineMap_mem_affineSpan_pair t _ _
    have hline : monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
      by_contra hne
      exact monsky_atomMidpoint_not_mem_distinct_faceLine
        T htriangle hcard hvolume f g e hef hne hmg
    have hgleft : monskyFaceLeft T htriangle g ∈ monskyFaceLine T htriangle g := by
      rw [monskyFaceLine]
      exact left_mem_affineSpan_pair ℝ _ _
    have hgright : monskyFaceRight T htriangle g ∈ monskyFaceLine T htriangle g := by
      rw [monskyFaceLine]
      exact right_mem_affineSpan_pair ℝ _ _
    have hgleft' : monskyFaceLeft T htriangle g ∈ monskyFaceLine T htriangle f := by
      rwa [hline]
    have hgright' : monskyFaceRight T htriangle g ∈ monskyFaceLine T htriangle f := by
      rwa [hline]
    rw [monskyFaceLine, mem_affineSpan_pair_iff_exists_lineMap_eq] at hgleft' hgright'
    obtain ⟨a, ha⟩ := hgleft'
    obtain ⟨b, hb⟩ := hgright'
    have hLinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hscalar : midpoint ℝ r q = AffineMap.lineMap a b t := by
      apply hLinj
      calc
        L (midpoint ℝ r q) = monskyAtomMidpoint e := hm.symm
        _ = G t := htm.symm
        _ = AffineMap.lineMap (L a) (L b) t := by rw [ha, hb]
        _ = L (AffineMap.lineMap a b t) := (L.apply_lineMap a b t).symm
    have hleftNode : monskyFaceLeft T htriangle g ∈ monskyNodes T htriangle :=
      monsky_faceLeft_mem_nodes T htriangle g
    have hrightNode : monskyFaceRight T htriangle g ∈ monskyNodes T htriangle :=
      monsky_faceRight_mem_nodes T htriangle g
    have haout : a ∉ Set.Ioo r q := by
      intro hain
      apply monsky_no_node_mem_openSegment_of_consecutive
        T htriangle hcard hvolume f hrq hleftNode
      rw [← image_openSegment ℝ L r q, openSegment_eq_Ioo hrqlt]
      exact ⟨a, hain, ha⟩
    have hbout : b ∉ Set.Ioo r q := by
      intro hbin
      apply monsky_no_node_mem_openSegment_of_consecutive
        T htriangle hcard hvolume f hrq hrightNode
      rw [← image_openSegment ℝ L r q, openSegment_eq_Ioo hrqlt]
      exact ⟨b, hbin, hb⟩
    have henclose := monsky_scalar_segment_enclosure hrqlt ht hscalar haout hbout
    have hrseg : r ∈ segment ℝ a b := by
      rcases henclose with henclose | henclose
      · exact Icc_subset_segment ⟨henclose.1, hrqlt.le.trans henclose.2⟩
      · rw [segment_symm]
        exact Icc_subset_segment ⟨henclose.1, hrqlt.le.trans henclose.2⟩
    have hqseg : q ∈ segment ℝ a b := by
      rcases henclose with henclose | henclose
      · exact Icc_subset_segment ⟨henclose.1.trans hrqlt.le, henclose.2⟩
      · rw [segment_symm]
        exact Icc_subset_segment ⟨henclose.1.trans hrqlt.le, henclose.2⟩
    have hLrseg : L r ∈ segment ℝ (monskyFaceLeft T htriangle g)
        (monskyFaceRight T htriangle g) := by
      rw [← ha, ← hb, ← image_segment ℝ L a b]
      exact ⟨r, hrseg, rfl⟩
    have hLqseg : L q ∈ segment ℝ (monskyFaceLeft T htriangle g)
        (monskyFaceRight T htriangle g) := by
      rw [← ha, ← hb, ← image_segment ℝ L a b]
      exact ⟨q, hqseg, rfl⟩
    have hrmem := monsky_fst_mem_of_mem_consecutivePairs hrq
    have hqmem := monsky_snd_mem_of_mem_consecutivePairs hrq
    have hLrNode := monsky_lineMap_mem_nodes_of_mem_paramList
      T htriangle hcard hvolume f hrmem
    have hLqNode := monsky_lineMap_mem_nodes_of_mem_paramList
      T htriangle hcard hvolume f hqmem
    have hLrPoint := monsky_mem_pointList_of_mem_nodes_of_mem_segment
      T htriangle hcard hvolume g hLrNode hLrseg
    have hLqPoint := monsky_mem_pointList_of_mem_nodes_of_mem_segment
      T htriangle hcard hvolume g hLqNode hLqseg
    rw [monskyFacePointList, List.mem_map] at hLrPoint hLqPoint
    obtain ⟨r', hr'mem, hr'eq⟩ := hLrPoint
    obtain ⟨q', hq'mem, hq'eq⟩ := hLqPoint
    have hGinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume g)
    have hrqne : L r ≠ L q := hLinj.ne hrqlt.ne
    have hr'q'ne : r' ≠ q' := by
      intro h
      apply hrqne
      rw [← hr'eq, ← hq'eq, h]
    rcases lt_or_gt_of_ne hr'q'ne with hr'q' | hq'r'
    · have hno : ∀ u ∈ monskyFaceParamList T htriangle g,
          ¬(r' < u ∧ u < q') := by
        intro u hu hubetween
        have huNode := monsky_lineMap_mem_nodes_of_mem_paramList
          T htriangle hcard hvolume g hu
        apply monsky_no_node_mem_openSegment_of_consecutive
          T htriangle hcard hvolume f hrq huNode
        rw [← hr'eq, ← hq'eq, ← image_openSegment ℝ G r' q',
          openSegment_eq_Ioo hr'q']
        exact ⟨u, hubetween, rfl⟩
      have hadj := monsky_mem_consecutivePairs_of_sortedLT
        (monsky_faceParamList_sorted T htriangle hcard hvolume g)
        hr'mem hq'mem hr'q' hno
      apply (monsky_mem_faceAtomList_iff T htriangle g e).2
      refine ⟨r', q', hadj, ?_⟩
      rw [heq, ← hr'eq, ← hq'eq]
    · have hno : ∀ u ∈ monskyFaceParamList T htriangle g,
          ¬(q' < u ∧ u < r') := by
        intro u hu hubetween
        have huNode := monsky_lineMap_mem_nodes_of_mem_paramList
          T htriangle hcard hvolume g hu
        apply monsky_no_node_mem_openSegment_of_consecutive
          T htriangle hcard hvolume f hrq huNode
        rw [← hq'eq, ← hr'eq, openSegment_symm, ← image_openSegment ℝ G q' r',
          openSegment_eq_Ioo hq'r']
        exact ⟨u, hubetween, rfl⟩
      have hadj := monsky_mem_consecutivePairs_of_sortedLT
        (monsky_faceParamList_sorted T htriangle hcard hvolume g)
        hq'mem hr'mem hq'r' hno
      apply (monsky_mem_faceAtomList_iff T htriangle g e).2
      refine ⟨q', r', hadj, ?_⟩
      rw [heq, ← hr'eq, ← hq'eq, Sym2.eq_swap]

end MetaMathlibExt
