/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Convex/Kirchberger.lean -/


import Def.Geometry.Convex.Kirchberger
import Lemma.Set.Convex.Kirchberger


namespace MetaMathlibExt

-- Failure of global strict separation is witnessed by at most `d + 2` points.
example (d : ℕ) (A B : Finset (EuclideanSpace ℝ (Fin d)))
    (hglobal : ¬ ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
      w ≠ 0 ∧ (∀ a ∈ A, inner ℝ w a < b) ∧
        ∀ c ∈ B, b < inner ℝ w c) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)), C ⊆ A ∪ B ∧ C.card ≤ d + 2 ∧
      ¬ ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
        w ≠ 0 ∧ (∀ a ∈ A ∩ C, inner ℝ w a < b) ∧
          ∀ c ∈ B ∩ C, b < inner ℝ w c := by
  classical
  by_contra hnoObstruction
  apply hglobal
  apply (kirchberger d A B).2
  intro C hC hcard
  by_contra hsep
  exact hnoObstruction ⟨C, hC, hcard, hsep⟩

end MetaMathlibExt
