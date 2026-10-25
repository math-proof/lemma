/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.ZMultiples
import Def.Geometry.Convex.PickTheorem.Part16
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_invariant_cut {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
    (hPcomp : IsCompact P) (hPint : (interior P).Nonempty) {A C : Fin 2 → ℤ}
    {b d y : Fin 2 → ℝ} (hAC : A ≠ C)
    (ha : pickCast A ∈ P.extremePoints ℝ) (hb : b ∈ P)
    (hc : pickCast C ∈ P.extremePoints ℝ) (hd : d ∈ P)
    (hyac : y ∈ openSegment ℝ (pickCast A) (pickCast C))
    (hybd : y ∈ openSegment ℝ b d) (hbline : b ∉ line[ℝ, pickCast A, pickCast C]) :
    pickInvariant P = pickInvariant (P ∩ pickHalfPlus (pickCast A) (pickCast C)) +
      pickInvariant (P ∩ pickHalfMinus (pickCast A) (pickCast C)) := by
  let a := pickCast A
  let c := pickCast C
  let Pp := P ∩ pickHalfPlus a c
  let Pm := P ∩ pickHalfMinus a c
  let L := pickLatticePoints P
  let Lp := pickLatticePoints Pp
  let Lm := pickLatticePoints Pm
  let I := pickLatticePoints (interior P)
  let Ip := pickLatticePoints (interior Pp)
  let Im := pickLatticePoints (interior Pm)
  let O := pickLatticePoints (openSegment ℝ a c)
  have hac : a ≠ c := fun hac ↦ hAC (pick_cast_injective hac)
  have hPpcomp : IsCompact Pp := hPcomp.inter_right (pick_halfPlus_isClosed a c)
  have hPmcomp : IsCompact Pm := hPcomp.inter_right (pick_halfMinus_isClosed a c)
  have hL : L.Finite := pick_lattice_preimage_finite hPcomp
  have hLp : Lp.Finite := pick_lattice_preimage_finite hPpcomp
  have hLm : Lm.Finite := pick_lattice_preimage_finite hPmcomp
  have hIp : Ip.Finite := by
    apply hLp.subset
    intro z hz
    change pickCast z ∈ Pp
    exact interior_subset hz
  have hIm : Im.Finite := by
    apply hLm.subset
    intro z hz
    change pickCast z ∈ Pm
    exact interior_subset hz
  have hI : I.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ P
    exact interior_subset hz
  have hO : O.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ P
    exact hP.segment_subset ha.1 hc.1 (openSegment_subset_segment ℝ a c hz)
  have hLunion : Lp ∪ Lm = L := by
    change pickCast ⁻¹' Pp ∪ pickCast ⁻¹' Pm = pickCast ⁻¹' P
    rw [← Set.preimage_union, pick_cut_union]
  have hLinter : Lp ∩ Lm = pickLatticePoints (segment ℝ a c) := by
    change pickCast ⁻¹' Pp ∩ pickCast ⁻¹' Pm = pickCast ⁻¹' segment ℝ a c
    rw [← Set.preimage_inter, pick_cut_inter hP hac ha hc]
  have hclosed := Set.ncard_union_add_ncard_inter Lp Lm hLp hLm
  rw [hLunion, hLinter] at hclosed
  have hsegment : (pickLatticePoints (segment ℝ a c)).ncard = O.ncard + 2 := by
    exact pick_lattice_segment_ncard hAC
  have hIset : I = (Ip ∪ Im) ∪ O := by
    change pickCast ⁻¹' interior P =
      (pickCast ⁻¹' interior Pp ∪ pickCast ⁻¹' interior Pm) ∪
        pickCast ⁻¹' openSegment ℝ a c
    rw [← Set.preimage_union, ← Set.preimage_union,
      pick_interior_cut hP hPint ha hb hc hd hac hyac hybd hbline]
  have hIpIm : Disjoint Ip Im := by
    rw [Set.disjoint_left]
    intro z hzp hzm
    have hp : pickNormal a c a < pickNormal a c (pickCast z) := by
      change pickCast z ∈ interior Pp at hzp
      rw [interior_inter, pick_interior_halfPlus hac] at hzp
      exact hzp.2
    have hm : pickNormal a c (pickCast z) < pickNormal a c a := by
      change pickCast z ∈ interior Pm at hzm
      rw [interior_inter, pick_interior_halfMinus hac] at hzm
      exact hzm.2
    linarith
  have hhalvesO : Disjoint (Ip ∪ Im) O := by
    rw [Set.disjoint_left]
    intro z hzhalf hzO
    have hzline : pickCast z ∈ line[ℝ, a, c] := by
      apply affineSegment_subset_affineSpan ℝ a c
      rw [affineSegment_eq_segment]
      exact openSegment_subset_segment ℝ a c hzO
    have hzeq : pickNormal a c (pickCast z) = pickNormal a c a := by
      have := (pick_side_eq_zero_iff_mem_line hac (pickCast z)).2 hzline
      dsimp only [pickSide] at this
      linarith
    rcases hzhalf with hzp | hzm
    · change pickCast z ∈ interior Pp at hzp
      rw [interior_inter, pick_interior_halfPlus hac] at hzp
      have hlt : pickNormal a c a < pickNormal a c (pickCast z) := hzp.2
      rw [hzeq] at hlt
      exact (lt_irrefl _ hlt).elim
    · change pickCast z ∈ interior Pm at hzm
      rw [interior_inter, pick_interior_halfMinus hac] at hzm
      have hlt : pickNormal a c (pickCast z) < pickNormal a c a := hzm.2
      rw [hzeq] at hlt
      exact (lt_irrefl _ hlt).elim
  have hhalfCard : (Ip ∪ Im).ncard = Ip.ncard + Im.ncard :=
    Set.ncard_union_eq hIpIm hIp hIm
  have hinter : I.ncard = Ip.ncard + Im.ncard + O.ncard := by
    rw [hIset, Set.ncard_union_eq hhalvesO (hIp.union hIm) hO, hhalfCard]
  have hclosedR := congrArg (fun n : ℕ ↦ (n : ℝ)) hclosed
  have hsegmentR := congrArg (fun n : ℕ ↦ (n : ℝ)) hsegment
  have hinterR := congrArg (fun n : ℕ ↦ (n : ℝ)) hinter
  push_cast at hclosedR hsegmentR hinterR
  change (L.ncard : ℝ) + I.ncard - 2 =
    ((Lp.ncard : ℝ) + Ip.ncard - 2) + ((Lm.ncard : ℝ) + Im.ncard - 2)
  linarith

theorem pick_origin_triangle_doubled (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    2 * (volume (pickTriangle u v h)).toReal = pickInvariant (pickTriangle u v h) := by
  have hformula := toReal_volume_convexHull_lattice_triangle u v h
  rw [← pick_triangle_eq_explicit u v h] at hformula
  change (volume (pickTriangle u v h)).toReal =
    (pickLatticePoints (interior (pickTriangle u v h))).ncard +
      (pickLatticePoints (frontier (pickTriangle u v h))).ncard / 2 - 1 at hformula
  have hLB := pick_lattice_ncard_eq_interior_add_frontier (pick_triangle_isCompact u v h)
  have hLBR := congrArg (fun n : ℕ ↦ (n : ℝ)) hLB
  push_cast at hLBR
  rw [pickInvariant]
  change 2 * (volume (pickTriangle u v h)).toReal =
    (pickLatticePoints (pickTriangle u v h)).ncard +
      (pickLatticePoints (interior (pickTriangle u v h))).ncard - 2
  linarith

theorem pick_triangle_doubled (p q r : Fin 2 → ℤ)
    (h : pickDet (q - p) (r - p) ≠ 0) :
    2 * (volume (convexHull ℝ
      ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)))).toReal =
      pickInvariant (convexHull ℝ
        ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ))) := by
  let T := pickTriangle (q - p) (r - p) h
  have hset : ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) =
      pickCast p +ᵥ ({0, pickCast (q - p), pickCast (r - p)} : Set (Fin 2 → ℝ)) := by
    rw [← Set.image_vadd]
    simp only [vadd_eq_add, Set.image_insert_eq, add_zero, Set.image_singleton]
    have hpq : pickCast p + pickCast (q - p) = pickCast q := by
      funext i
      simp [pickCast]
    have hpr : pickCast p + pickCast (r - p) = pickCast r := by
      funext i
      simp [pickCast]
    rw [hpq, hpr]
  have htriangle : convexHull ℝ
        ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) = pickCast p +ᵥ T := by
    rw [hset, convexHull_vadd]
    change pickCast p +ᵥ convexHull ℝ
      ({0, pickCast (q - p), pickCast (r - p)} : Set (Fin 2 → ℝ)) = pickCast p +ᵥ T
    rw [← pick_triangle_eq_explicit]
  rw [htriangle, pick_volume_vadd, pick_invariant_vadd]
  exact pick_origin_triangle_doubled (q - p) (r - p) h

theorem pick_polygon_doubled (vertices : Finset (Fin 2 → ℤ))
    (hfull : (interior (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
    2 * (volume (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ))))).toReal =
      pickInvariant (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ)))) := by
  classical
  induction vertices using Finset.strongInductionOn with
  | _ vertices ih =>
    let X := pickCast '' (vertices : Set (Fin 2 → ℤ))
    let P := convexHull ℝ X
    let E := vertices.filter fun z ↦ pickCast z ∈ P.extremePoints ℝ
    have hXfin : X.Finite := vertices.finite_toSet.image pickCast
    have hPconv : Convex ℝ P := convex_convexHull ℝ X
    have hPcomp : IsCompact P := hXfin.isCompact_convexHull ℝ
    have hEP : pickCast '' (E : Set (Fin 2 → ℤ)) = P.extremePoints ℝ := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Finset.mem_filter.mp hz).2
      · intro hx
        rcases extremePoints_convexHull_subset hx with ⟨z, hz, rfl⟩
        exact ⟨z, Finset.mem_filter.mpr ⟨hz, hx⟩, rfl⟩
    have hPhull : convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) = P := by
      calc
        convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) =
            closure (convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ)))) :=
          ((E.finite_toSet.image pickCast).isCompact_convexHull ℝ).isClosed.closure_eq.symm
        _ = P := by
          rw [hEP]
          exact closure_convexHull_extremePoints hPcomp hPconv
    have hspan : affineSpan ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) = ⊤ := by
      apply affineSpan_eq_top_of_nonempty_interior
      rw [hPhull]
      exact hfull
    by_cases hsmall : E.card ≤ 3
    · have hlarge : 3 ≤ E.card := by
        by_contra h
        have hcard : E.card ≤ 2 := by omega
        have hnotop := affineSpan_image_ne_top_of_encard_le_finrank ℝ E.finite_toSet
          (p := pickCast) (by
            rw [Set.encard_coe_eq_coe_finsetCard, Module.finrank_fin_fun]
            exact_mod_cast hcard)
        exact hnotop hspan
      have hcard : E.card = 3 := by omega
      obtain ⟨e : Fin 3 ↪ (Fin 2 → ℤ), he⟩ :=
        Function.Embedding.exists_of_card_eq_finset (s := E) (α := Fin 3)
          (by simpa using hcard.symm)
      have herange : Set.range e = (E : Set (Fin 2 → ℤ)) := by
        have hcoe := congrArg (fun s : Finset (Fin 2 → ℤ) ↦ (s : Set (Fin 2 → ℤ))) he
        simpa using hcoe
      let p := e 0
      let q := e 1
      let r := e 2
      have htriple : pickCast '' (E : Set (Fin 2 → ℤ)) =
          ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [← herange] at hz
          rcases hz with ⟨i, rfl⟩
          fin_cases i <;> simp [p, q, r]
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rintro (rfl | rfl | rfl)
          · exact ⟨p, herange ▸ Set.mem_range_self 0, rfl⟩
          · exact ⟨q, herange ▸ Set.mem_range_self 1, rfl⟩
          · exact ⟨r, herange ▸ Set.mem_range_self 2, rfl⟩
      have hpq : pickCast p ≠ pickCast q := by
        intro hpq
        have hzeroone : (0 : Fin 3) = 1 := e.injective (pick_cast_injective hpq)
        norm_num at hzeroone
      have hdet : pickDet (q - p) (r - p) ≠ 0 := by
        intro hdet
        have hrline : pickCast r ∈ line[ℝ, pickCast p, pickCast q] := by
          apply (pick_side_eq_zero_iff_mem_line hpq (pickCast r)).1
          rw [pick_side_apply]
          norm_num [pickDet, pickCast] at hdet ⊢
          exact_mod_cast hdet
        have hle : affineSpan ℝ
            ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) ≤
              line[ℝ, pickCast p, pickCast q] := by
          apply affineSpan_le.2
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact left_mem_affineSpan_pair ℝ _ _
          · exact right_mem_affineSpan_pair ℝ _ _
          · exact hrline
        rw [← htriple, hspan] at hle
        exact pick_line_ne_top hpq (top_unique hle)
      change 2 * (volume P).toReal = pickInvariant P
      rw [← hPhull, htriple]
      exact pick_triangle_doubled p q r hdet
    · have hEcard : 4 ≤ E.card := by omega
      obtain ⟨e : Fin 4 ↪ (Fin 2 → ℤ), he⟩ :=
        Function.Embedding.exists_of_card_le_finset (s := E) (α := Fin 4)
          (by simpa using hEcard)
      let g : Fin 4 → (Fin 2 → ℝ) := fun i ↦ pickCast (e i)
      have hge (i : Fin 4) : g i ∈ P.extremePoints ℝ := by
        have hei := he (Set.mem_range_self i)
        change e i ∈ vertices.filter (fun z ↦ pickCast z ∈ P.extremePoints ℝ) at hei
        change pickCast (e i) ∈ P.extremePoints ℝ
        exact (Finset.mem_filter.mp hei).2
      let ee : Fin 4 ↪ P.extremePoints ℝ :=
        ⟨fun i ↦ ⟨g i, hge i⟩, fun i j hij ↦ e.injective
          (pick_cast_injective (Subtype.ext_iff.mp hij))⟩
      have hgconv : ConvexIndependent ℝ g := by
        intro s i hi
        by_contra his
        have hiext := (hPconv.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).mp (hge i)
        apply hiext.2
        apply convexHull_mono _ hi
        rintro _ ⟨j, hjs, rfl⟩
        refine ⟨(hge j).1, ?_⟩
        rw [Set.mem_singleton_iff]
        intro hji
        have : j = i := e.injective (pick_cast_injective hji)
        exact his (this ▸ hjs)
      have hgdep : ¬AffineIndependent ℝ g := by
        apply (finrank_vectorSpan_le_iff_not_affineIndependent ℝ g (n := 2) (by simp)).1
        simpa [Module.finrank_fin_fun] using (vectorSpan ℝ (Set.range g)).finrank_le
      obtain ⟨I, y, hyI, hyIc⟩ := Convex.radon_partition hgdep
      have hparts := pick_radon_parts_two hgconv ⟨y, hyI, hyIc⟩
      obtain ⟨i₀, i₁, hi₀i₁, hI⟩ := Set.ncard_eq_two.mp hparts.1
      obtain ⟨j₀, j₁, hj₀j₁, hIc⟩ := Set.ncard_eq_two.mp hparts.2
      have hi₀ : i₀ ∈ I := by simp [hI]
      have hi₁ : i₁ ∈ I := by simp [hI]
      have hj₀ : j₀ ∈ Iᶜ := by simp [hIc]
      have hj₁ : j₁ ∈ Iᶜ := by simp [hIc]
      have hyac : y ∈ openSegment ℝ (g i₀) (g i₁) := by
        apply mem_openSegment_of_ne_left_right
        · intro hiy
          exact ((hgconv.mem_convexHull_iff Iᶜ i₀).mp (by simpa [hiy] using hyIc)) hi₀
        · intro hiy
          exact ((hgconv.mem_convexHull_iff Iᶜ i₁).mp (by simpa [hiy] using hyIc)) hi₁
        · rw [← convexHull_pair, ← Set.image_pair, ← hI]
          exact hyI
      have hybd : y ∈ openSegment ℝ (g j₀) (g j₁) := by
        apply mem_openSegment_of_ne_left_right
        · intro hjy
          exact hj₀ ((hgconv.mem_convexHull_iff I j₀).mp (by simpa [hjy] using hyI))
        · intro hjy
          exact hj₁ ((hgconv.mem_convexHull_iff I j₁).mp (by simpa [hjy] using hyI))
        · rw [← convexHull_pair, ← Set.image_pair, ← hIc]
          exact hyIc
      have hj₀i₀ : j₀ ≠ i₀ := fun h ↦ hj₀ (h ▸ hi₀)
      have hj₀i₁ : j₀ ≠ i₁ := fun h ↦ hj₀ (h ▸ hi₁)
      have hbline : g j₀ ∉ line[ℝ, g i₀, g i₁] := by
        intro hbline
        exact pick_not_collinear_of_convexIndependent hgconv hj₀i₀ hi₀i₁ hj₀i₁
          (collinear_insert_of_mem_affineSpan_pair hbline)
      have hprod : pickSide (g i₀) (g i₁) (g j₀) *
          pickSide (g i₀) (g i₁) (g j₁) < 0 :=
        pick_side_mul_side_neg_of_cross (fun h ↦ hi₀i₁ (e.injective
          (pick_cast_injective h))) hyac hybd hbline
      have hAV : e i₀ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self i₀))).1
      have hCV : e i₁ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self i₁))).1
      have hj₀V : e j₀ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self j₀))).1
      have hj₁V : e j₁ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self j₁))).1
      have finish (B D : Fin 2 → ℤ) (hBV : B ∈ vertices) (hDV : D ∈ vertices)
          (hBpos : 0 < pickSide (g i₀) (g i₁) (pickCast B))
          (hDneg : pickSide (g i₀) (g i₁) (pickCast D) < 0)
          (hyBD : y ∈ openSegment ℝ (pickCast B) (pickCast D)) :
          2 * (volume P).toReal = pickInvariant P := by
        let Vp := vertices.filter fun z ↦ pickCast z ∈ pickHalfPlus (g i₀) (g i₁)
        let Vm := vertices.filter fun z ↦ pickCast z ∈ pickHalfMinus (g i₀) (g i₁)
        have hVp_lt : Vp ⊂ vertices := by
          rw [Finset.filter_ssubset]
          exact ⟨D, hDV, by rw [pick_mem_halfPlus_iff]; linarith⟩
        have hVm_lt : Vm ⊂ vertices := by
          rw [Finset.filter_ssubset]
          exact ⟨B, hBV, by rw [pick_mem_halfMinus_iff]; linarith⟩
        have hXp : pickCast '' (Vp : Set (Fin 2 → ℤ)) =
            X ∩ pickHalfPlus (g i₀) (g i₁) := by
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨⟨z, (Finset.mem_filter.mp hz).1, rfl⟩, (Finset.mem_filter.mp hz).2⟩
          · rintro ⟨⟨z, hz, rfl⟩, hzhalf⟩
            exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzhalf⟩, rfl⟩
        have hXm : pickCast '' (Vm : Set (Fin 2 → ℤ)) =
            X ∩ pickHalfMinus (g i₀) (g i₁) := by
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨⟨z, (Finset.mem_filter.mp hz).1, rfl⟩, (Finset.mem_filter.mp hz).2⟩
          · rintro ⟨⟨z, hz, rfl⟩, hzhalf⟩
            exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzhalf⟩, rfl⟩
        have hAC : e i₀ ≠ e i₁ := fun h ↦ hi₀i₁ (e.injective h)
        have hac : g i₀ ≠ g i₁ := fun h ↦ hAC (pick_cast_injective h)
        have ha : g i₀ ∈ P.extremePoints ℝ := hge i₀
        have hc : g i₁ ∈ P.extremePoints ℝ := hge i₁
        have hHullp : convexHull ℝ (pickCast '' (Vp : Set (Fin 2 → ℤ))) =
            P ∩ pickHalfPlus (g i₀) (g i₁) := by
          rw [hXp]
          exact pick_convexHull_inter_halfPlus hXfin hac ha hc
        have hHullm : convexHull ℝ (pickCast '' (Vm : Set (Fin 2 → ℤ))) =
            P ∩ pickHalfMinus (g i₀) (g i₁) := by
          rw [hXm]
          exact pick_convexHull_inter_halfMinus hXfin hac ha hc
        have hBP : pickCast B ∈ P := subset_convexHull ℝ X ⟨B, hBV, rfl⟩
        have hDP : pickCast D ∈ P := subset_convexHull ℝ X ⟨D, hDV, rfl⟩
        have hfullp : (interior (convexHull ℝ
            (pickCast '' (Vp : Set (Fin 2 → ℤ))))).Nonempty := by
          rw [hHullp]
          exact pick_interior_inter_halfPlus_nonempty hPconv hPcomp.isClosed hfull hac hBP hBpos
        have hfullm : (interior (convexHull ℝ
            (pickCast '' (Vm : Set (Fin 2 → ℤ))))).Nonempty := by
          rw [hHullm]
          exact pick_interior_inter_halfMinus_nonempty hPconv hPcomp.isClosed hfull hac hDP hDneg
        have hpickp := ih Vp hVp_lt hfullp
        have hpickm := ih Vm hVm_lt hfullm
        rw [hHullp] at hpickp
        rw [hHullm] at hpickm
        have hvol := pick_volume_cut hPconv hPcomp hac ha hc
        have hBline : pickCast B ∉ line[ℝ, g i₀, g i₁] := by
          intro hline
          have := (pick_side_eq_zero_iff_mem_line hac (pickCast B)).2 hline
          linarith
        have hinv := pick_invariant_cut hPconv hPcomp hfull hAC ha hBP hc hDP hyac hyBD hBline
        linarith
      rcases mul_neg_iff.mp hprod with ⟨hj₀pos, hj₁neg⟩ | ⟨hj₀neg, hj₁pos⟩
      · exact finish (e j₀) (e j₁) hj₀V hj₁V hj₀pos hj₁neg hybd
      · exact finish (e j₁) (e j₀) hj₁V hj₀V hj₁pos hj₀neg
          (by simpa [openSegment_symm ℝ] using hybd)

/-- Pick's area formula for convex standard-lattice polygons:
`area = I + B / 2 - 1`, where `I` counts interior lattice points and `B`
counts boundary lattice points. The polygon is the full-dimensional convex
hull of finitely many integer-coordinate vertices (`hfull` rules out
degenerate cases); `B` counts integer points on the frontier of the hull.

Sources: Eugen J. Ionascu, "A Parametrization of Equilateral Triangles
Having Integer Coordinates", Journal of Integer Sequences 10 (2007),
Article 07.6.7, standard formula `Area = #b / 2 + #i - 1`, lines 87–100,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Ionascu/ionascu2.tex>;
Kevin A. Broughan, "The gcd-sum function", Journal of Integer Sequences 4
(2001), Article 01.2.2, trapezium application, lines 699–715 (the prose
there prints "+1" but the paper's own derived formula, equation label `10`,
uses the minus-one form),
<https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex>;
Gil Alon and Pete L. Clark, "On the Number of Representations of an
Integer by a Linear Form", Journal of Integer Sequences 8 (2005),
Article 05.5.2, generalized lattice version
`A(P) = δ * (h + b / 2 - 1)`, lines 633–638 (this module is the `δ = 1`
standard-lattice case),
<https://cs.uwaterloo.ca/journals/JIS/VOL8/Clark/clark80.tex>.

Proves `Wanted` entry `pick_convex_lattice_polygon`.

Proof: The triangle case counts lattice points in a half-open fundamental
parallelogram. A crossing diagonal then cuts larger polygons into two smaller
full-dimensional lattice polygons, allowing strong induction on the vertex set.
-/
theorem pick_convex_lattice_polygon (vertices : Finset (Fin 2 → ℤ))
    (hfull :
      (interior
        (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
    (volume
      (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).toReal =
      (Set.ncard {z : Fin 2 → ℤ |
        (fun i => (z i : ℝ)) ∈
          interior
            (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))} : ℝ) +
        (Set.ncard {z : Fin 2 → ℤ |
          (fun i => (z i : ℝ)) ∈
            frontier
              (convexHull ℝ
                ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))} : ℝ) / 2 - 1 := by
  let P := convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ)))
  have hPcomp : IsCompact P :=
    (vertices.finite_toSet.image pickCast).isCompact_convexHull ℝ
  have hdoubled := pick_polygon_doubled vertices hfull
  change 2 * (volume P).toReal = pickInvariant P at hdoubled
  rw [pickInvariant] at hdoubled
  have hLB := pick_lattice_ncard_eq_interior_add_frontier hPcomp
  have hLBR := congrArg (fun n : ℕ ↦ (n : ℝ)) hLB
  push_cast at hLBR
  change (volume P).toReal =
    (pickLatticePoints (interior P)).ncard +
      (pickLatticePoints (frontier P)).ncard / 2 - 1
  linarith

end MetaMathlibExt
