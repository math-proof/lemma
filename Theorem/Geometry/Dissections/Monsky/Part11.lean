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
import Def.Geometry.Dissections.Monsky.Part11
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

@[simp] lemma monsky_atomWeight_mk (V : ValuationSubring ℝ)
    (a b : EuclideanSpace ℝ (Fin 2)) :
    monskyAtomWeight V s(a, b) =
      monskyEdgeWeight (monskyColor V a) (monskyColor V b) := by
  rfl

lemma monsky_facePointList_nodup
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFacePointList T htriangle f).Nodup := by
  rw [monskyFacePointList]
  exact (monsky_faceParamList_sorted T htriangle hcard hvolume f).nodup.map
    (AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f))

lemma monsky_faceAtomList_nodup
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFaceAtomList T htriangle f).Nodup := by
  rw [monskyFaceAtomList]
  exact monsky_sym2_consecutivePairs_nodup _
    (monsky_facePointList_nodup T htriangle hcard hvolume f)

lemma monsky_sum_atoms_weighted_faceIndicator (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) :
    ∑ e ∈ monskyAtoms T htriangle,
        monskyAtomWeight V e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle f) =
      ((monskyFaceAtomList T htriangle f).map (monskyAtomWeight V)).sum := by
  classical
  let s := (monskyFaceAtomList T htriangle f).toFinset
  have hsubset : s ⊆ monskyAtoms T htriangle := by
    intro e he
    simp only [s, List.mem_toFinset] at he
    simp only [monskyAtoms, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨f, by simpa using he⟩
  calc
    _ = ∑ e ∈ monskyAtoms T htriangle,
        if e ∈ s then monskyAtomWeight V e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hes : e ∈ s
      · have hesList : e ∈ monskyFaceAtomList T htriangle f := by
          simpa only [s, List.mem_toFinset] using hes
        simp [monskyIndicator, hes, hesList]
      · have henot : e ∉ monskyFaceAtomList T htriangle f := by
          simpa only [s, List.mem_toFinset] using hes
        simp [monskyIndicator, hes, henot]
    _ = ∑ e ∈ s, if e ∈ s then monskyAtomWeight V e else 0 := by
      symm
      apply Finset.sum_subset hsubset
      intro e he henot
      simp [henot]
    _ = ∑ e ∈ s, monskyAtomWeight V e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [he]
    _ = _ := List.sum_toFinset (monskyAtomWeight V)
      (monsky_faceAtomList_nodup T htriangle hcard hvolume f)

lemma monsky_faceEndpointWeight_eq_sum_atoms (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) :
    monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle f))
        (monskyColor V (monskyFaceRight T htriangle f)) =
      ∑ e ∈ monskyAtoms T htriangle,
        monskyAtomWeight V e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle f) :=
  (monsky_sum_faceAtomWeight V T htriangle f).symm.trans
    (monsky_sum_atoms_weighted_faceIndicator
      V T htriangle hcard hvolume f).symm

lemma monsky_triangle_boundary_eq_atom_sum (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
          (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) =
      ∑ e ∈ monskyAtoms T htriangle, monskyAtomWeight V e *
        ∑ t : ↑T, ∑ i : Fin 3,
          monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
  classical
  let A := monskyAtoms T htriangle
  let w := monskyAtomWeight V
  calc
    _ = ∑ t : ↑T, ∑ i : Fin 3, ∑ e ∈ A,
        w e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro i hi
      exact monsky_faceEndpointWeight_eq_sum_atoms
        V T htriangle hcard hvolume (.inl (t, i))
    _ = ∑ t : ↑T, ∑ e ∈ A, w e * ∑ i : Fin 3,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact monsky_sum_weighted_swap A w _
    _ = _ := by
      exact monsky_sum_weighted_swap A w _

lemma monsky_square_boundary_eq_atom_sum (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    ∑ i : Fin 4,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inr i)))
          (monskyColor V (monskyFaceRight T htriangle (.inr i))) =
      ∑ e ∈ monskyAtoms T htriangle, monskyAtomWeight V e *
        ∑ i : Fin 4,
          monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
  classical
  let A := monskyAtoms T htriangle
  let w := monskyAtomWeight V
  calc
    _ = ∑ i : Fin 4, ∑ e ∈ A,
        w e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact monsky_faceEndpointWeight_eq_sum_atoms
        V T htriangle hcard hvolume (.inr i)
    _ = ∑ e ∈ A, w e * ∑ i : Fin 4,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) :=
      monsky_sum_weighted_swap A w _

lemma monsky_boundary_weight_identity (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
          (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) =
      ∑ i : Fin 4,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inr i)))
          (monskyColor V (monskyFaceRight T htriangle (.inr i))) := by
  rw [monsky_triangle_boundary_eq_atom_sum V T htriangle hcard hvolume,
    monsky_square_boundary_eq_atom_sum V T htriangle hcard hvolume]
  apply Finset.sum_congr rfl
  intro e he
  apply congrArg (monskyAtomWeight V e * ·)
  obtain ⟨f, hef⟩ := monsky_atom_mem_exists_face T htriangle he
  exact monsky_atom_incidence_parity
    T htriangle hcard hvolume hcover hdisjoint f e hef

lemma monsky_exists_rainbow_triangle (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior) :
    ∃ (t : ↑T) (a b c : EuclideanSpace ℝ (Fin 2)),
      t.1 = convexHull ℝ {a, b, c} ∧
        monskyColor V a = 0 ∧ monskyColor V b = 1 ∧ monskyColor V c = 2 := by
  have hsum : ∑ t : ↑T, ∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) = 1 :=
    (monsky_boundary_weight_identity
      V T htriangle hcard hvolume hcover hdisjoint).trans
      (monsky_square_boundary_weight_eq_one V T htriangle)
  have hsumne : (∑ t : ↑T, ∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i))))) ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨t, _, htne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have htone : (∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i))))) = 1 :=
    (monsky_zmod_two_eq_zero_or_one _).resolve_left htne
  let v := monskyVertices T htriangle t
  have hcycle :
      monskyEdgeWeight (monskyColor V (v 1)) (monskyColor V (v 2)) +
          monskyEdgeWeight (monskyColor V (v 2)) (monskyColor V (v 0)) +
        monskyEdgeWeight (monskyColor V (v 0)) (monskyColor V (v 1)) = 1 := by
    simpa [Fin.sum_univ_three, monskyFaceLeft, monskyFaceRight, v] using htone
  obtain ⟨h12, h20, h01⟩ :=
    (monskyEdgeWeight_triangle
      (monskyColor V (v 1)) (monskyColor V (v 2)) (monskyColor V (v 0))).1 hcycle
  let colorIndex : Fin 3 → Fin 3 := fun i ↦ monskyColor V (v i)
  have hinj : Function.Injective colorIndex := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [colorIndex]
  have hsurj : Function.Surjective colorIndex := Empty.Finite.surjective_of_injective hinj
  obtain ⟨i0, hi0⟩ := hsurj 0
  obtain ⟨i1, hi1⟩ := hsurj 1
  obtain ⟨i2, hi2⟩ := hsurj 2
  have hindices : ∀ i : Fin 3, i = i0 ∨ i = i1 ∨ i = i2 := by
    intro i
    have hc : colorIndex i = 0 ∨ colorIndex i = 1 ∨ colorIndex i = 2 := by
      generalize hci : colorIndex i = ci
      fin_cases ci <;> simp_all
    rcases hc with hc | hc | hc
    · exact Or.inl (hinj (hc.trans hi0.symm))
    · exact Or.inr (Or.inl (hinj (hc.trans hi1.symm)))
    · exact Or.inr (Or.inr (hinj (hc.trans hi2.symm)))
  have hrange : ({v i0, v i1, v i2} : Set (EuclideanSpace ℝ (Fin 2))) = Set.range v := by
    ext x
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨i0, rfl⟩
      · exact ⟨i1, rfl⟩
      · exact ⟨i2, rfl⟩
    · rintro ⟨i, rfl⟩
      rcases hindices i with rfl | rfl | rfl <;> simp
  refine ⟨t, v i0, v i1, v i2, ?_, hi0, hi1, hi2⟩
  rw [monsky_vertices_spec T htriangle t, ← hrange]

/-- Monsky's theorem (statement_id `monsky-s1`): a dissection of a square into
finitely many triangles of equal area (an equidissection) uses an even number
of triangles.

Source: Paul Monsky, "On Dividing A Square Into Triangles," *The American Mathematical
Monthly* 77(2) (1970), 161–164, DOI 10.1080/00029890.1970.11992441.

Proves `Wanted` entry `monsky_theorem`.

Proof: A 2-adic valuation on ℝ gives a three-colouring of the plane, and a Sperner-type parity
count supplies a rainbow triangle whose area valuation rules out an odd number of pieces.
-/
theorem monsky_theorem :
    ∀ (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
      (∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2), t = convexHull ℝ {a, b, c}) →
      Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
        {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} →
      (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior →
      (∃ A : ENNReal, ∀ t ∈ T, MeasureTheory.volume t = A) →
      Even T.card := by
  intro T htriangle hcover hdisjoint hcommon
  obtain ⟨A, hA⟩ := hcommon
  have hsum := monsky_sum_volume_eq_one T htriangle hcover hdisjoint
  obtain ⟨hcard, hvolume⟩ := monsky_common_volume_eq_card_inv T hsum A hA
  obtain ⟨V, hint, htwo⟩ := monsky_exists_valuation_int_le_one_two_lt_one
  obtain ⟨t, a, b, c, htabc, ha, hb, hc⟩ :=
    monsky_exists_rainbow_triangle
      V T htriangle hcard hvolume hcover hdisjoint
  by_contra heven
  exact monsky_odd_card_contradiction V hint htwo T
    (Nat.not_even_iff_odd.mp heven) hvolume t.2 a b c htabc ha hb hc

end MetaMathlibExt
