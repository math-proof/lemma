import Mathlib
import sympy.Basic
import Def.Geometry.Convex.Kirchberger
open MetaMathlibExt


namespace MetaMathlibExt

/--
[kirchberger_halfspace_convex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean)
-/
@[path]
private lemma kirchberger_halfspace_convex {d : ℕ}
  (i : EuclideanSpace ℝ (Fin d) ⊕ EuclideanSpace ℝ (Fin d)) :
  Convex ℝ (kirchberger_halfspace i) := by
  obtain a | c := i
  · have hlin : IsLinearMap ℝ
    (fun p : EuclideanSpace ℝ (Fin d) × ℝ => inner ℝ p.1 a - p.2) := by
    constructor
    · intro x y
      simp [inner_add_left]
      ring
    · intro r x
      simp [inner_smul_left]
      ring
    simpa [kirchberger_halfspace, sub_lt_zero] using convex_halfSpace_lt hlin 0
  · have hlin : IsLinearMap ℝ
    (fun p : EuclideanSpace ℝ (Fin d) × ℝ => p.2 - inner ℝ p.1 c) := by
    constructor
    · intro x y
      simp [inner_add_left]
      ring
    · intro r x
      simp [inner_smul_left]
      ring
    simpa [kirchberger_halfspace, sub_lt_zero] using convex_halfSpace_lt hlin 0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kirchberger_small_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean)
-/
@[path]
private lemma kirchberger_small_intersection {d : ℕ}
  {A B : Finset (EuclideanSpace ℝ (Fin d))}
  (hlocal : ∀ C : Finset (EuclideanSpace ℝ (Fin d)), C ⊆ A ∪ B →
    C.card ≤ d + 2 → ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
      w ≠ 0 ∧ (∀ a ∈ A ∩ C, inner ℝ w a < b) ∧
        ∀ c ∈ B ∩ C, b < inner ℝ w c)
  {I : Finset (EuclideanSpace ℝ (Fin d) ⊕ EuclideanSpace ℝ (Fin d))}
  (hI : I ⊆ A.disjSum B) (hcard : I.card ≤ d + 2) :
  (⋂ i ∈ I, kirchberger_halfspace i).Nonempty := by
  classical
  let C := I.image (Sum.elim id id)
  have hCsub : C ⊆ A ∪ B := by
    intro x hx
    simp only [C, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    obtain a | c := i
    · simp only [Sum.elim_inl, Finset.mem_union]
      exact Or.inl (by simpa using hI hi)
    · simp only [Sum.elim_inr, Finset.mem_union]
      exact Or.inr (by simpa using hI hi)
  have hCcard : C.card ≤ d + 2 := by
    have hCcardI : C.card ≤ I.card := by
      simpa [C] using Finset.card_image_le (s := I) (f := Sum.elim id id)
    exact hCcardI.trans hcard
  obtain ⟨w, b, _, hA, hB⟩ := hlocal C hCsub hCcard
  refine ⟨(w, b), ?_⟩
  simp only [Set.mem_iInter]
  intro i hi
  obtain a | c := i
  · change inner ℝ w a < b
    apply hA a
    simp only [Finset.mem_inter]
    exact ⟨by simpa using hI hi, by simp [C, hi]⟩
  · change b < inner ℝ w c
    apply hB c
    simp only [Finset.mem_inter]
    exact ⟨by simpa using hI hi, by simp [C, hi]⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kirchberger_helly_witness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean)
-/
@[path]
private lemma kirchberger_helly_witness {d : ℕ}
  {A B : Finset (EuclideanSpace ℝ (Fin d))}
  (hlocal : ∀ C : Finset (EuclideanSpace ℝ (Fin d)), C ⊆ A ∪ B →
    C.card ≤ d + 2 → ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
      w ≠ 0 ∧ (∀ a ∈ A ∩ C, inner ℝ w a < b) ∧
        ∀ c ∈ B ∩ C, b < inner ℝ w c) :
  ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
    (∀ a ∈ A, inner ℝ w a < b) ∧ ∀ c ∈ B, b < inner ℝ w c := by
  classical
  have hall :
    (⋂ i ∈ A.disjSum B, kirchberger_halfspace i).Nonempty := by
    apply Convex.helly_theorem' (𝕜 := ℝ)
    · intro i _
      exact kirchberger_halfspace_convex i
    · intro I hI hcard
      apply kirchberger_small_intersection hlocal hI
      simpa [Module.finrank_prod] using hcard
  obtain ⟨p, hp⟩ := hall
  simp only [Set.mem_iInter] at hp
  refine ⟨p.1, p.2, ?_, ?_⟩
  · intro a ha
    simpa [kirchberger_halfspace] using hp (Sum.inl a) (by simpa using ha)
  · intro c hc
    simpa [kirchberger_halfspace] using hp (Sum.inr c) (by simpa using hc)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kirchberger_nonzero_direction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean)
-/
@[path]
private lemma kirchberger_nonzero_direction {d : ℕ}
  {A B : Finset (EuclideanSpace ℝ (Fin d))}
  (hlocal : ∀ C : Finset (EuclideanSpace ℝ (Fin d)), C ⊆ A ∪ B →
    C.card ≤ d + 2 → ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
      w ≠ 0 ∧ (∀ a ∈ A ∩ C, inner ℝ w a < b) ∧
        ∀ c ∈ B ∩ C, b < inner ℝ w c)
  {w : EuclideanSpace ℝ (Fin d)} {b : ℝ}
  (hA : ∀ a ∈ A, inner ℝ w a < b) (hB : ∀ c ∈ B, b < inner ℝ w c) :
  ∃ w' : EuclideanSpace ℝ (Fin d), ∃ b' : ℝ,
    w' ≠ 0 ∧ (∀ a ∈ A, inner ℝ w' a < b') ∧
      ∀ c ∈ B, b' < inner ℝ w' c := by
  classical
  by_cases hw : w ≠ 0
  · exact ⟨w, b, hw, hA, hB⟩
  have hw0 : w = 0 := by simpa using hw
  have hempty : A = ∅ ∨ B = ∅ := by
    obtain hAe | ⟨a, ha⟩ := A.eq_empty_or_nonempty
    · exact Or.inl hAe
    obtain hBe | ⟨c, hc⟩ := B.eq_empty_or_nonempty
    · exact Or.inr hBe
    have ha0 := hA a ha
    have hc0 := hB c hc
    simp [hw0] at ha0 hc0
    linarith
  obtain ⟨v, _, hv, _, _⟩ := hlocal ∅ (by simp) (by simp)
  obtain hAe | hBe := hempty
  · refine ⟨v, -(∑ c ∈ B, |inner ℝ v c|) - 1, hv, ?_, ?_⟩
    · simp [hAe]
    · intro c hc
      have hterm : |inner ℝ v c| ≤ ∑ x ∈ B, |inner ℝ v x| :=
        Finset.single_le_sum (s := B) (f := fun x ↦ |inner ℝ v x|)
          (fun _ _ ↦ abs_nonneg _) hc
      have hneg : -inner ℝ v c ≤ |inner ℝ v c| := neg_le_abs _
      linarith
  · refine ⟨v, (∑ a ∈ A, |inner ℝ v a|) + 1, hv, ?_, ?_⟩
    · intro a ha
      have hterm : |inner ℝ v a| ≤ ∑ x ∈ A, |inner ℝ v x| :=
        Finset.single_le_sum (s := A) (f := fun x ↦ |inner ℝ v x|)
          (fun _ _ ↦ abs_nonneg _) ha
      have hle : inner ℝ v a ≤ |inner ℝ v a| := le_abs_self _
      linarith
    · simp [hBe]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kirchberger_forward](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean)
-/
@[path]
private lemma kirchberger_forward {d : ℕ}
  {A B : Finset (EuclideanSpace ℝ (Fin d))}
  (hsep : ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
    w ≠ 0 ∧ (∀ a ∈ A, inner ℝ w a < b) ∧
      ∀ c ∈ B, b < inner ℝ w c) :
  ∀ C : Finset (EuclideanSpace ℝ (Fin d)), C ⊆ A ∪ B → C.card ≤ d + 2 →
    ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
      w ≠ 0 ∧ (∀ a ∈ A ∩ C, inner ℝ w a < b) ∧
        ∀ c ∈ B ∩ C, b < inner ℝ w c := by
  intro C _ _
  obtain ⟨w, b, hw, hA, hB⟩ := hsep
  refine ⟨w, b, hw, ?_, ?_⟩
  · intro a ha
    exact hA a (Finset.mem_inter.mp ha).1
  · intro c hc
    exact hB c (Finset.mem_inter.mp hc).1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kirchberger_backward](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean)
-/
@[path]
private lemma kirchberger_backward {d : ℕ}
  {A B : Finset (EuclideanSpace ℝ (Fin d))}
  (hlocal : ∀ C : Finset (EuclideanSpace ℝ (Fin d)), C ⊆ A ∪ B →
    C.card ≤ d + 2 → ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
      w ≠ 0 ∧ (∀ a ∈ A ∩ C, inner ℝ w a < b) ∧
        ∀ c ∈ B ∩ C, b < inner ℝ w c) :
  ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
    w ≠ 0 ∧ (∀ a ∈ A, inner ℝ w a < b) ∧
      ∀ c ∈ B, b < inner ℝ w c := by
  obtain ⟨w, b, hA, hB⟩ := kirchberger_helly_witness hlocal
  exact kirchberger_nonzero_direction hlocal hA hB

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kirchberger](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean)
-/
@[path]
lemma kirchberger
  :
-- imply
  ∀ (d : ℕ) (A B : Finset (EuclideanSpace ℝ (Fin d))),
    (∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
    w ≠ 0 ∧ (∀ a ∈ A, inner ℝ w a < b) ∧ (∀ c ∈ B, b < inner ℝ w c)) ↔
    ∀ C : Finset (EuclideanSpace ℝ (Fin d)), C ⊆ A ∪ B → C.card ≤ d + 2 →
    ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
    w ≠ 0 ∧ (∀ a ∈ A ∩ C, inner ℝ w a < b) ∧
    (∀ c ∈ B ∩ C, b < inner ℝ w c) := by
-- proof
  intro d A B
  constructor
  · exact kirchberger_forward
  · exact kirchberger_backward

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
