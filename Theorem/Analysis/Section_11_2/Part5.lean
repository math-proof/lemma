module

public import Mathlib
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Instance.Analysis.Section_11_1.Part8
public import Abbrev.Analysis.Section_11_2.Part5

public section
/-!
# Analysis I, Section 11.2: Piecewise constant functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Piecewise constant functions.
- The piecewise constant integral.

-/


namespace Chapter11

open BoundedInterval
open MeasureTheory

private theorem toReal_ofReal_max (x : ℝ) : (ENNReal.ofReal x).toReal = max x 0 := by
  by_cases h : 0 ≤ x
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · have hx : x ≤ 0 := le_of_not_ge h
    rw [ENNReal.ofReal_of_nonpos hx, ENNReal.toReal_zero, max_eq_right hx]

private theorem volume_toReal (J : BoundedInterval) :
    (volume (J : Set ℝ)).toReal = J.length := by
  cases J with
  | Ioo a b =>
    simp [BoundedInterval.length, Real.volume_Ioo, set_Ioo]
    exact toReal_ofReal_max (b - a)
  | Icc a b =>
    simp [BoundedInterval.length, Real.volume_Icc, set_Icc]
    exact toReal_ofReal_max (b - a)
  | Ioc a b =>
    simp [BoundedInterval.length, Real.volume_Ioc, set_Ioc]
    exact toReal_ofReal_max (b - a)
  | Ico a b =>
    simp [BoundedInterval.length, Real.volume_Ico, set_Ico]
    exact toReal_ofReal_max (b - a)

private theorem volume_eq_ofReal (J : BoundedInterval) :
    volume (J : Set ℝ) = ENNReal.ofReal J.length := by
  have hfin : volume (J : Set ℝ) ≠ ⊤ := by
    cases J with
    | Ioo a b => simp [set_Ioo, Real.volume_Ioo]
    | Icc a b => simp [set_Icc, Real.volume_Icc]
    | Ioc a b => simp [set_Ioc, Real.volume_Ioc]
    | Ico a b => simp [set_Ico, Real.volume_Ico]
  rw [← ENNReal.ofReal_toReal hfin, volume_toReal J]

private theorem length_of_empty_set {J : BoundedInterval} (hJ : (J : Set ℝ) = ∅) :
    J.length = 0 := by
  have : volume (J : Set ℝ) = 0 := by simp [hJ]
  simpa [this] using (volume_toReal J).symm

private theorem measurable_interval (J : BoundedInterval) : MeasurableSet (J : Set ℝ) := by
  cases J with
  | Ioo a b => simp [set_Ioo]
  | Icc a b => simp [set_Icc]
  | Ioc a b => simp [set_Ioc]
  | Ico a b => simp [set_Ico]

private theorem sum_length_of {K : BoundedInterval} (R : Partition K) :
    ∑ J ∈ R.intervals, J.length = K.length := by
  have hdisj : Set.PairwiseDisjoint (R.intervals : Set BoundedInterval)
      (fun J : BoundedInterval => (J : Set ℝ)) := by
    intro J hJ L hL hJL
    refine Set.disjoint_left.mpr ?_
    intro x hxJ hxL
    have hxK : x ∈ (K : Set ℝ) := (subset_iff _ _).mp (R.contains J hJ) hxJ
    exact hJL ((R.exists_unique x hxK).unique ⟨hJ, hxJ⟩ ⟨hL, hxL⟩)
  have hunion : (⋃ J ∈ R.intervals, (J : Set ℝ)) = (K : Set ℝ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨J, hJ, hxJ⟩ := Set.mem_iUnion₂.mp hx
      exact (subset_iff _ _).mp (R.contains J hJ) hxJ
    · intro hx
      refine Set.mem_iUnion₂.mpr ?_
      obtain ⟨J, hJ⟩ := (R.exists_unique x hx).exists
      exact ⟨J, hJ.1, hJ.2⟩
  have hmeas : ∀ J ∈ R.intervals, MeasurableSet (J : Set ℝ) :=
    fun J _ => measurable_interval J
  have hvol : volume (K : Set ℝ) = ∑ J ∈ R.intervals, volume (J : Set ℝ) := by
    rw [← hunion, measure_biUnion_finset hdisj hmeas]
  have hfin : ∀ J ∈ R.intervals, volume (J : Set ℝ) ≠ ⊤ := by
    intro J _; rw [volume_eq_ofReal]; exact ENNReal.ofReal_ne_top
  calc
    ∑ J ∈ R.intervals, J.length
        = ∑ J ∈ R.intervals, (volume (J : Set ℝ)).toReal := by
          apply Finset.sum_congr rfl; intro J _; exact (volume_toReal J).symm
    _ = (∑ J ∈ R.intervals, volume (J : Set ℝ)).toReal := (ENNReal.toReal_sum hfin).symm
    _ = (volume (K : Set ℝ)).toReal := by rw [hvol]
    _ = K.length := volume_toReal K

public theorem PiecewiseConstantWith.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f P = integ g P := by
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  simp [constant_value_on]
  congr
  have := P.contains _ hJ
  grind [subset_iff]

private theorem const_mul_length {f:ℝ → ℝ} {I: BoundedInterval} {R: Partition I}
    {L J : BoundedInterval} (hR : PiecewiseConstantWith f R)
    (hJ : J ∈ R.intervals) (hsub : L ⊆ J) :
    constant_value_on f (L : Set ℝ) * L.length =
      constant_value_on f (J : Set ℝ) * L.length := by
  by_cases hne : (L : Set ℝ).Nonempty
  · obtain ⟨c, hc⟩ := hR J hJ
    have hCL : ConstantOn f (L : Set ℝ) :=
      ⟨c, fun x => hc ⟨x.1, (subset_iff _ _).mp hsub x.2⟩⟩
    have hLc : constant_value_on f (L : Set ℝ) = c := by
      rw [constant_value_on, constant_value, dif_pos hCL]
      obtain ⟨x, hxL⟩ := hne
      have hfL : f x = hCL.choose := hCL.choose_spec ⟨x, hxL⟩
      have hfJ : f x = c := hc ⟨x, (subset_iff _ _).mp hsub hxL⟩
      exact hfL.symm.trans hfJ
    have hJc : constant_value_on f (J : Set ℝ) = c := by
      have hCJ : ConstantOn f (J : Set ℝ) := hR J hJ
      rw [constant_value_on, constant_value, dif_pos hCJ]
      obtain ⟨x, hxL⟩ := hne
      have hxJ := (subset_iff _ _).mp hsub hxL
      have hfJ' : f x = hCJ.choose := hCJ.choose_spec ⟨x, hxJ⟩
      have hfJ : f x = c := hc ⟨x, hxJ⟩
      exact hfJ'.symm.trans hfJ
    simp [hLc, hJc]
  · have hlen0 : L.length = 0 :=
      length_of_empty_set (Set.not_nonempty_iff_eq_empty.mp hne)
    simp [hlen0]

private theorem inter_set_comm (J K : BoundedInterval) :
    ((J ∩ K : BoundedInterval) : Set ℝ) = ((K ∩ J : BoundedInterval) : Set ℝ) := by
  ext x
  constructor
  · intro hx
    exact (mem_inter K J x).mpr (And.symm ((mem_inter J K x).mp hx))
  · intro hx
    exact (mem_inter J K x).mpr (And.symm ((mem_inter K J x).mp hx))

private theorem sum_inter_length {I: BoundedInterval} (R S : Partition I)
    {J : BoundedInterval} (hJ : J ∈ R.intervals) :
    ∑ K ∈ S.intervals, (J ∩ K).length = J.length := by
  let RJ : Partition J := {
    intervals := S.intervals.image (fun B => J ∩ B)
    exists_unique := by
      intro x hx
      have hxI : x ∈ (I : Set ℝ) := (subset_iff _ _).mp (R.contains J hJ) hx
      obtain ⟨B, hB⟩ := (S.exists_unique x hxI).exists
      refine ExistsUnique.intro (J ∩ B) ?_ ?_
      · exact ⟨Finset.mem_image.mpr ⟨B, hB.1, rfl⟩, (mem_inter J B x).mpr ⟨hx, hB.2⟩⟩
      · intro L hL
        obtain ⟨hLim, hxL⟩ := hL
        obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hLim
        have hxB' : x ∈ B' := ((mem_inter J B' x).mp hxL).2
        have hBeq : B' = B := (S.exists_unique x hxI).unique ⟨hB', hxB'⟩ hB
        subst hBeq
        rfl
    contains := by
      intro L hL
      obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hL
      intro y hy
      exact ((mem_inter J B y).mp hy).1
  }
  have hsumRJ : ∑ L ∈ RJ.intervals, L.length = J.length := sum_length_of RJ
  have himg : RJ.intervals = S.intervals.image (fun B => J ∩ B) := rfl
  rw [← hsumRJ, himg]
  have hmaps : ∀ K ∈ S.intervals, (J ∩ K) ∈ S.intervals.image (fun B => J ∩ B) :=
    fun K hK => Finset.mem_image.mpr ⟨K, hK, rfl⟩
  have hfiber :
      ∑ K ∈ S.intervals, (J ∩ K).length =
        ∑ L ∈ S.intervals.image (fun B => J ∩ B),
          ∑ K ∈ S.intervals.filter (fun B => J ∩ B = L), L.length :=
    (Finset.sum_fiberwise_of_maps_to' (t := S.intervals.image (fun B => J ∩ B))
      hmaps (fun L => L.length)).symm
  refine hfiber.trans ?_
  apply Finset.sum_congr rfl
  intro L hL
  by_cases hne : (L : Set ℝ).Nonempty
  · obtain ⟨B, hB, hBL⟩ := Finset.mem_image.mp hL
    have hfilter : S.intervals.filter (fun K => J ∩ K = L) = {B} := by
      ext K
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hK
        obtain ⟨x, hxL⟩ := hne
        have hKe : J ∩ K = L := hK.2
        have hxK : x ∈ K := ((mem_inter J K x).mp (hKe ▸ hxL)).2
        have hxB : x ∈ B := ((mem_inter J B x).mp (hBL ▸ hxL)).2
        have hxI : x ∈ (I : Set ℝ) :=
          (subset_iff _ _).mp (R.contains J hJ) ((mem_inter J B x).mp (hBL ▸ hxL)).1
        exact (S.exists_unique x hxI).unique ⟨hK.1, hxK⟩ ⟨hB, hxB⟩
      · intro hKB
        subst hKB
        exact ⟨hB, hBL⟩
    simp [hfilter]
  · have hlen0 : L.length = 0 :=
      length_of_empty_set (Set.not_nonempty_iff_eq_empty.mp hne)
    simp [hlen0]

/-- Proposition 11.2.13 (Piecewise constant integral is independent of partition) / Exercise 11.2.3 -/
public theorem PiecewiseConstantWith.integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
    (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') : integ f P = integ f P' := by
  classical
  let g (L : BoundedInterval) := constant_value_on f (L : Set ℝ) * L.length
  have g_empty {L : BoundedInterval} (hL : (L : Set ℝ) = ∅) : g L = 0 := by
    simp [g, length_of_empty_set hL]
  have g_inter_comm (J K : BoundedInterval) : g (J ∩ K) = g (K ∩ J) := by
    have hset := inter_set_comm J K
    have hlen : (J ∩ K).length = (K ∩ J).length := by
      rw [← volume_toReal, ← volume_toReal, hset]
    simp only [g]
    rw [hset, hlen]
  have expand (R S : Partition I) (hR : PiecewiseConstantWith f R) :
      integ f R = ∑ J ∈ R.intervals, ∑ K ∈ S.intervals, g (J ∩ K) ∧
      integ f (max R S) = ∑ J ∈ R.intervals, ∑ K ∈ S.intervals, g (J ∩ K) := by
    have hdouble :
        ∑ J ∈ R.intervals, ∑ K ∈ S.intervals, g (J ∩ K) =
          ∑ J ∈ R.intervals, constant_value_on f (J : Set ℝ) * J.length := by
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [g]
      have : ∀ K ∈ S.intervals,
          constant_value_on f ((J ∩ K : BoundedInterval) : Set ℝ) * (J ∩ K).length =
            constant_value_on f (J : Set ℝ) * (J ∩ K).length := by
        intro K _
        refine const_mul_length hR hJ ?_
        intro x hx
        exact ((mem_inter J K x).mp hx).1
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_inter_length (hJ := hJ)]
    have hR_eq : integ f R = ∑ J ∈ R.intervals, ∑ K ∈ S.intervals, g (J ∩ K) := by
      unfold integ
      exact hdouble.symm
    have hQ : (max R S).intervals = R.intervals.image₂ (fun J K => J ∩ K) S.intervals := rfl
    have hmaps : ∀ p ∈ R.intervals ×ˢ S.intervals,
        p.1 ∩ p.2 ∈ (max R S).intervals := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      rw [hQ]
      exact Finset.mem_image₂.mpr ⟨p.1, h1, p.2, h2, rfl⟩
    have hprod :
        ∑ J ∈ R.intervals, ∑ K ∈ S.intervals, g (J ∩ K) =
          ∑ p ∈ R.intervals ×ˢ S.intervals, g (p.1 ∩ p.2) :=
      (Finset.sum_product' R.intervals S.intervals (fun J K => g (J ∩ K))).symm
    have hfiber :
        ∑ L ∈ (max R S).intervals,
            ∑ p ∈ (R.intervals ×ˢ S.intervals).filter (fun p => p.1 ∩ p.2 = L), g L =
          ∑ p ∈ R.intervals ×ˢ S.intervals, g (p.1 ∩ p.2) :=
      Finset.sum_fiberwise_of_maps_to' (t := (max R S).intervals) hmaps (fun L => g L)
    have himage :
        ∑ L ∈ (max R S).intervals, g L =
          ∑ p ∈ R.intervals ×ˢ S.intervals, g (p.1 ∩ p.2) := by
      refine Eq.trans ?_ hfiber
      apply Finset.sum_congr rfl
      intro L hL
      by_cases hne : (L : Set ℝ).Nonempty
      · have hL' : L ∈ R.intervals.image₂ (fun J K => J ∩ K) S.intervals := by
          rwa [hQ] at hL
        obtain ⟨J, hJ, K, hK, hJK⟩ := Finset.mem_image₂.mp hL'
        have hfilter :
            (R.intervals ×ˢ S.intervals).filter (fun p => p.1 ∩ p.2 = L) = {(J, K)} := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
          constructor
          · intro hp
            obtain ⟨x, hxL⟩ := hne
            have hpe : p.1 ∩ p.2 = L := hp.2
            have hx1 : x ∈ p.1 := ((mem_inter p.1 p.2 x).mp (hpe ▸ hxL)).1
            have hx2 : x ∈ p.2 := ((mem_inter p.1 p.2 x).mp (hpe ▸ hxL)).2
            have hxJ : x ∈ J := ((mem_inter J K x).mp (hJK ▸ hxL)).1
            have hxK : x ∈ K := ((mem_inter J K x).mp (hJK ▸ hxL)).2
            have hxI : x ∈ (I : Set ℝ) := (subset_iff _ _).mp (R.contains J hJ) hxJ
            have hp1 : p.1 = J :=
              (R.exists_unique x hxI).unique ⟨hp.1.1, hx1⟩ ⟨hJ, hxJ⟩
            have hp2 : p.2 = K :=
              (S.exists_unique x hxI).unique ⟨hp.1.2, hx2⟩ ⟨hK, hxK⟩
            exact Prod.ext hp1 hp2
          · rintro rfl
            exact ⟨⟨hJ, hK⟩, hJK⟩
        simp [hfilter, g]
      · have : g L = 0 := g_empty (Set.not_nonempty_iff_eq_empty.mp hne)
        simp [this]
    have hmax_eq : integ f (max R S) = ∑ J ∈ R.intervals, ∑ K ∈ S.intervals, g (J ∩ K) := by
      unfold integ
      exact himage.trans hprod.symm
    exact ⟨hR_eq, hmax_eq⟩
  have hPmax := expand P P' hP
  have hP'max := expand P' P hP'
  have hmaxes :
      ∑ J ∈ P.intervals, ∑ K ∈ P'.intervals, g (J ∩ K) =
        ∑ K ∈ P'.intervals, ∑ J ∈ P.intervals, g (K ∩ J) := by
    refine (Finset.sum_congr rfl ?_).trans Finset.sum_comm
    intro J _
    refine Finset.sum_congr rfl ?_
    intro K _
    exact g_inter_comm J K
  calc
    integ f P = ∑ J ∈ P.intervals, ∑ K ∈ P'.intervals, g (J ∩ K) := hPmax.1
    _ = ∑ K ∈ P'.intervals, ∑ J ∈ P.intervals, g (K ∩ J) := hmaxes
    _ = integ f P' := hP'max.1.symm

end Chapter11
