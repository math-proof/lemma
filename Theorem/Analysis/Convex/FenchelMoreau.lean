import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Convex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Def.Analysis.Convex.FenchelMoreau
/-!
# Fenchel conjugates and epigraph API

Foundation for the Fenchel–Moreau theorem: a proper lsc convex
`f : E → EReal` on a Hausdorff locally convex real tvs equals its
biconjugate. This module provides the conjugate/biconjugate definitions in
the exact shape of `banach_limit`-style wanted statements and the
closed-epigraph API (convexity is definitional from the hypothesis;
closedness is the continuous preimage of the `EReal` epigraph).

References: Werner Fenchel, *Convex Cones, Sets, and Functions: From Notes
by D. W. Blackett of Lectures at Princeton University, 1951*, Princeton
University Department of Mathematics, 1953, Open Library OL1430688W; and
Jean-Jacques Moreau, "Fonctions convexes duales et points proximaux,"
C. R. Acad. Sci. Paris 255 (1962), 2897–2899, zbMATH 0118.10502.
-/


namespace Convex.FenchelMoreau

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- The `ℝ`-threshold epigraph is the preimage of the `EReal` epigraph. -/
lemma epi_eq_preimage (f : E → EReal) :
    {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}
      = (fun p : E × ℝ => (p.1, ((p.2 : ℝ) : EReal))) ⁻¹'
        {q : E × EReal | f q.1 ≤ q.2} := by
  ext ⟨x, r⟩
  rfl

omit [AddCommGroup E] [Module ℝ E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- A lower-semicontinuous function's `ℝ`-threshold epigraph is closed. -/
theorem isClosed_epi_real (f : E → EReal) (hf_lsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  rw [epi_eq_preimage]
  apply IsClosed.preimage _ hf_lsc.isClosed_epigraph
  exact continuous_fst.prodMk
    (EReal.continuous_coe_iff.mpr continuous_snd)

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- Easy direction of Fenchel–Moreau: the biconjugate never exceeds `f`. -/
theorem biconj_le (f : E → EReal) (hf_not_bot : ∀ x, f x ≠ ⊥) (x : E) :
    fenchelBiconj f x ≤ f x := by
  unfold fenchelBiconj
  apply ciSup_le
  intro L
  by_cases hfx : f x = ⊤
  · rw [hfx]
    exact le_top
  · apply EReal.sub_le_of_le_add
    have h1 : (((L x : ℝ)) : EReal) - f x ≤ fenchelConj f L := by
      unfold fenchelConj
      exact le_iSup (fun y => (((L y : ℝ)) : EReal) - f y) x
    have h2 : f x + ((((L x : ℝ)) : EReal) - f x)
        ≤ f x + fenchelConj f L :=
      add_le_add le_rfl h1
    have h3 : (((L x : ℝ)) : EReal) = f x + ((((L x : ℝ)) : EReal) - f x) := by
      lift f x to ℝ using ⟨hfx, hf_not_bot x⟩ with s
      rw [← EReal.coe_sub, ← EReal.coe_add]
      congr 1
      ring
    rw [h3]
    exact h2

end Convex.FenchelMoreau
