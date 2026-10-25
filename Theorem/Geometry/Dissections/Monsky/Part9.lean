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
import Def.Geometry.Dissections.Monsky.Part9
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma monsky_faceLine_eq_of_atomMidpoint_mem
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (g : MonskyFace T)
    (hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g) :
    monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
  by_contra hne
  exact monsky_atomMidpoint_not_mem_distinct_faceLine
    T htriangle hcard hvolume f g e hef hne hmg

lemma monsky_triangle_atom_occ_iff
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (t : ↑T) (i : Fin 3) :
    e ∈ monskyFaceAtomList T htriangle (.inl (t, i)) ↔
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i))
          (monskyAtomMidpoint e) = 0 ∧
        ∀ j, j ≠ i →
          0 < monskyFaceForm T htriangle hcard hvolume (.inl (t, j))
            (monskyAtomMidpoint e) := by
  rw [monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e hef]
  simpa only [monskyFaceLeft, monskyFaceRight, monskyFaceForm,
    monsky_triangleBasis_apply] using
    (monsky_mem_open_affineBasis_face_iff
      (monskyTriangleBasis T htriangle hcard hvolume t) i (monskyAtomMidpoint e))

lemma monsky_square_atom_occ_iff
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (i : Fin 4) :
    e ∈ monskyFaceAtomList T htriangle (.inr i) ↔
      monskyFaceForm T htriangle hcard hvolume (.inr i) (monskyAtomMidpoint e) = 0 ∧
        ∀ j, j ≠ i →
          0 < monskyFaceForm T htriangle hcard hvolume (.inr j)
            (monskyAtomMidpoint e) := by
  rw [monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e hef]
  simpa only [monskyFaceForm] using
    (monsky_mem_open_square_face_iff T htriangle i (monskyAtomMidpoint e))

lemma monsky_triangle_atom_unique_zero
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (t : ↑T) (i j : Fin 3)
    (hi : monskyFaceForm T htriangle hcard hvolume (.inl (t, i))
      (monskyAtomMidpoint e) = 0)
    (hj : monskyFaceForm T htriangle hcard hvolume (.inl (t, j))
      (monskyAtomMidpoint e) = 0) : i = j := by
  have hmi := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inl (t, i)) (monskyAtomMidpoint e)).2 hi
  have hmj := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inl (t, j)) (monskyAtomMidpoint e)).2 hj
  have hfi := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inl (t, i)) hmi
  have hfj := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inl (t, j)) hmj
  exact monsky_triangle_faceLine_injective T htriangle hcard hvolume t
    (hfi.symm.trans hfj)

lemma monsky_square_atom_unique_zero
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (i j : Fin 4)
    (hi : monskyFaceForm T htriangle hcard hvolume (.inr i)
      (monskyAtomMidpoint e) = 0)
    (hj : monskyFaceForm T htriangle hcard hvolume (.inr j)
      (monskyAtomMidpoint e) = 0) : i = j := by
  have hmi := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inr i) (monskyAtomMidpoint e)).2 hi
  have hmj := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inr j) (monskyAtomMidpoint e)).2 hj
  have hfi := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inr i) hmi
  have hfj := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inr j) hmj
  exact monsky_square_faceLine_injective T htriangle hcard hvolume (hfi.symm.trans hfj)

lemma monsky_triangle_atom_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f)
    (p n : EuclideanSpace ℝ (Fin 2))
    (hstable : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g p ∧
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g n)
    (hflip : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
        monskyFaceForm T htriangle hcard hvolume g p *
          monskyFaceForm T htriangle hcard hvolume g n < 0)
    (t : ↑T) :
    ∑ i : Fin 3, monskyIndicator
        (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) =
      monskyIndicator (p ∈ t.1) + monskyIndicator (n ∈ t.1) := by
  have h := monsky_form_parity
    (m := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume
      (.inl (t, i)) (monskyAtomMidpoint e))
    (p := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) p)
    (n := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) n)
    (occ := fun i : Fin 3 ↦ e ∈ monskyFaceAtomList T htriangle (.inl (t, i)))
    (monsky_triangle_atom_unique_zero T htriangle hcard hvolume f e hef t)
    (fun i ↦ hstable (.inl (t, i))) (fun i ↦ hflip (.inl (t, i)))
    (monsky_triangle_atom_occ_iff T htriangle hcard hvolume f e hef t)
  calc
    _ = monskyIndicator (∀ i : Fin 3,
          0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) p) +
        monskyIndicator (∀ i : Fin 3,
          0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) n) := h
    _ = _ := congrArg₂ (· + ·)
      (congrArg monskyIndicator
        (propext (monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t p))).symm
      (congrArg monskyIndicator
        (propext (monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t n))).symm

lemma monsky_square_atom_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f)
    (p n : EuclideanSpace ℝ (Fin 2))
    (hstable : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g p ∧
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g n)
    (hflip : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
        monskyFaceForm T htriangle hcard hvolume g p *
          monskyFaceForm T htriangle hcard hvolume g n < 0) :
    ∑ i : Fin 4, monskyIndicator
        (e ∈ monskyFaceAtomList T htriangle (.inr i)) =
      monskyIndicator
          (p ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) +
        monskyIndicator
          (n ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) := by
  have h := monsky_form_parity
    (m := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume
      (.inr i) (monskyAtomMidpoint e))
    (p := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume (.inr i) p)
    (n := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume (.inr i) n)
    (occ := fun i : Fin 4 ↦ e ∈ monskyFaceAtomList T htriangle (.inr i))
    (monsky_square_atom_unique_zero T htriangle hcard hvolume f e hef)
    (fun i ↦ hstable (.inr i)) (fun i ↦ hflip (.inr i))
    (monsky_square_atom_occ_iff T htriangle hcard hvolume f e hef)
  calc
    _ = monskyIndicator (∀ i : Fin 4, 0 ≤ monskySquareSideForm i p) +
        monskyIndicator (∀ i : Fin 4, 0 ≤ monskySquareSideForm i n) := by
      simpa only [monskyFaceForm] using h
    _ = _ := congrArg₂ (· + ·)
      (congrArg monskyIndicator
        (propext (monsky_mem_unitSquare_iff_faceForms p))).symm
      (congrArg monskyIndicator
        (propext (monsky_mem_unitSquare_iff_faceForms n))).symm

lemma monsky_tile_membership_unique
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (x : EuclideanSpace ℝ (Fin 2))
    (hface : ∀ (t : ↑T) (i : Fin 3),
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x ≠ 0)
    (t u : ↑T) (hxt : x ∈ t.1) (hxu : x ∈ u.1) : t = u := by
  apply Subtype.ext
  apply hdisjoint.elim t.2 u.2
  apply Set.not_disjoint_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · apply (monsky_mem_interior_tile_iff_faceForms
      T htriangle hcard hvolume t x).2
    intro i
    exact lt_of_le_of_ne
      ((monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t x).1 hxt i)
      (Ne.symm (hface t i))
  · apply (monsky_mem_interior_tile_iff_faceForms
      T htriangle hcard hvolume u x).2
    intro i
    exact lt_of_le_of_ne
      ((monsky_mem_tile_iff_faceForms T htriangle hcard hvolume u x).1 hxu i)
      (Ne.symm (hface u i))

lemma monsky_sum_tile_indicator_eq_square
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (x : EuclideanSpace ℝ (Fin 2))
    (hface : ∀ (t : ↑T) (i : Fin 3),
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x ≠ 0) :
    ∑ t : ↑T, monskyIndicator (x ∈ t.1) =
      monskyIndicator
        (x ∈ {y : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ y.ofLp i ∧ y.ofLp i ≤ 1}) := by
  apply monsky_sum_indicator_eq_indicator_of_unique
  · constructor
    · intro hx
      have hxunion : x ∈ Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) :=
        hcover.symm ▸ hx
      obtain ⟨s, hsT, hxs⟩ := Set.mem_sUnion.mp hxunion
      exact ⟨⟨s, hsT⟩, hxs⟩
    · rintro ⟨t, hxt⟩
      rw [← hcover]
      exact Set.mem_sUnion_of_mem hxt t.2
  · intro t u hxt hxu
    exact monsky_tile_membership_unique
      T htriangle hcard hvolume hdisjoint x hface t u hxt hxu

lemma monsky_atom_incidence_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) =
      ∑ i : Fin 4,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
  obtain ⟨p, n, hstable, hflip⟩ :=
    monsky_exists_atom_probes T htriangle hcard hvolume f e hef
  have hne := monsky_probe_faceForms_ne_zero
    T htriangle hcard hvolume e p n hstable hflip
  have hp := monsky_sum_tile_indicator_eq_square
    T htriangle hcard hvolume hcover hdisjoint p (fun t i ↦ (hne (.inl (t, i))).1)
  have hn := monsky_sum_tile_indicator_eq_square
    T htriangle hcard hvolume hcover hdisjoint n (fun t i ↦ (hne (.inl (t, i))).2)
  calc
    _ = ∑ t : ↑T, (monskyIndicator (p ∈ t.1) + monskyIndicator (n ∈ t.1)) :=
      Finset.sum_congr rfl fun t _ ↦
        monsky_triangle_atom_parity
          T htriangle hcard hvolume f e hef p n hstable hflip t
    _ = (∑ t : ↑T, monskyIndicator (p ∈ t.1)) +
        ∑ t : ↑T, monskyIndicator (n ∈ t.1) := Finset.sum_add_distrib
    _ = monskyIndicator
          (p ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) +
        monskyIndicator
          (n ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) := by
      rw [hp, hn]
    _ = _ := (monsky_square_atom_parity
      T htriangle hcard hvolume f e hef p n hstable hflip).symm

end MetaMathlibExt
