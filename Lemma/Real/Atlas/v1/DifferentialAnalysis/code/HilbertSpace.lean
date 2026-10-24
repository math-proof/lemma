import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
open HilbertSpace
open scoped ComplexInnerProductSpace
open MeasureTheory Complex
open scoped ComplexConjugate ComplexInnerProductSpace


namespace HilbertSpace

/--
[exists_smallest_norm_of_closed_convex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma exists_smallest_norm_of_closed_convex
  [NormedAddCommGroup V]
  [IsHilbertSpace V]
  {C : Set V}
-- given
  (hne : C.Nonempty)
  (hclosed : IsClosed C)
  (hconvex : Convex ℝ C) :
-- imply
  ∃ v ∈ C, ‖v‖ = ⨅ w : C, ‖(w : V)‖ := by
-- proof
  letI : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  haveI : Nonempty ↥C := hne.to_subtype
  have hcomplete : IsComplete C := hclosed.isComplete
  obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex 0
  refine ⟨v, hv, ?_⟩
  simp only [zero_sub, norm_neg] at hmin
  exact hmin

end HilbertSpace

namespace HilbertSpace

/--
[unique_smallest_norm_of_closed_convex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma unique_smallest_norm_of_closed_convex
  [NormedAddCommGroup V]
  [IsHilbertSpace V]
  {C : Set V}
  {v v' : V}
-- given
  (hne : C.Nonempty)
  (hclosed : IsClosed C)
  (hconvex : Convex ℝ C)
  (hv : v ∈ C)
  (hv' : v' ∈ C)
  (hmin_v : ‖v‖ = ⨅ w : C, ‖(w : V)‖)
  (hmin_v' : ‖v'‖ = ⨅ w : C, ‖(w : V)‖) :
-- imply
  v = v' := by
-- proof
  letI : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  haveI : Nonempty ↥C := hne.to_subtype
  have para := parallelogram_law_with_norm (𝕜 := ℝ) v v'
  set δ := ⨅ w : C, ‖(w : V)‖ with hδ_def
  have hδ_nn : 0 ≤ δ := le_ciInf fun ⟨w, _⟩ => norm_nonneg w
  rw [hmin_v, hmin_v'] at para
  have hmid : (2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • v' ∈ C := by
    have h2 : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
    exact hconvex hv hv' (by positivity) (by positivity) h2
  have hmid_norm : δ ≤ ‖(2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • v'‖ := by
    have hbdd : BddBelow (Set.range fun (w : ↥C) => ‖(w : V)‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
    exact ciInf_le hbdd ⟨(2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • v', hmid⟩
  have hmid_eq : ‖(2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • v'‖ = ‖v + v'‖ / 2 := by
    rw [← smul_add, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]
    ring
  have key : ‖v - v'‖ ^ 2 ≤ 0 := by
    have h1 : ‖v + v'‖ ^ 2 + ‖v - v'‖ ^ 2 = 2 * (δ ^ 2 + δ ^ 2) := para
    have h2 : δ ≤ ‖v + v'‖ / 2 := by linarith [hmid_norm, hmid_eq]
    have h3 : 4 * δ ^ 2 ≤ ‖v + v'‖ ^ 2 := by nlinarith
    linarith
  have : ‖v - v'‖ = 0 := by nlinarith [sq_nonneg ‖v - v'‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end HilbertSpace

namespace HilbertSpace

/--
[exists_unique_smallest_norm_of_closed_convex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma exists_unique_smallest_norm_of_closed_convex
  [NormedAddCommGroup V]
  [IsHilbertSpace V]
  {C : Set V}
-- given
  (hne : C.Nonempty)
  (hclosed : IsClosed C)
  (hconvex : Convex ℝ C) :
-- imply
  ∃! v ∈ C, ‖v‖ = ⨅ w : C, ‖(w : V)‖ := by
-- proof
  obtain ⟨v, hv, hmin⟩ := exists_smallest_norm_of_closed_convex hne hclosed hconvex
  refine ⟨v, ⟨hv, hmin⟩, ?_⟩
  intro v' ⟨hv', hmin'⟩
  exact unique_smallest_norm_of_closed_convex hne hclosed hconvex hv' hv hmin' hmin

end HilbertSpace

namespace HilbertSpace

/--
[riesz_representation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma riesz_representation
  [NormedAddCommGroup V]
  [IsHilbertSpace V]
  {L : V →L[ℂ] ℂ} :
-- imply
  ∃! v : V, ∀ u : V, L u = ⟪v, u⟫ := by
-- proof
  refine ⟨(InnerProductSpace.toDual ℂ V).symm L, ?_, ?_⟩
  · intro u
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)).symm
  · intro v' hv'
    have hv_repr : ∀ u, L u = ⟪(InnerProductSpace.toDual ℂ V).symm L, u⟫ :=
      fun u => (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)).symm
    have : ∀ u, ⟪v', u⟫ = ⟪(InnerProductSpace.toDual ℂ V).symm L, u⟫ :=
      fun u => by rw [← hv', ← hv_repr]
    exact ext_inner_right ℂ this
end HilbertSpace
namespace HilbertSpace
open MeasureTheory Complex
open scoped ComplexConjugate ComplexInnerProductSpace

end HilbertSpace

namespace HilbertSpace

/--
[l2_dual_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma l2_dual_eq_integral
  [MeasurableSpace α]
  {μ : Measure α}
  {L : (α →₂[μ] ℂ) →L[ℂ] ℂ} :
-- imply
  ∃ g : α →₂[μ] ℂ, ∀ f : α →₂[μ] ℂ, L f = ∫ a, f a * starRingEnd ℂ (g a) ∂μ := by
-- proof
  obtain ⟨g, rfl⟩ := (InnerProductSpace.toDual ℂ (α →₂[μ] ℂ)).surjective L
  refine ⟨g, fun f => ?_⟩
  simp only [InnerProductSpace.toDual_apply_apply]
  rw [L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun a => RCLike.inner_apply _ _)
end HilbertSpace



-- created on 2026-10-23
