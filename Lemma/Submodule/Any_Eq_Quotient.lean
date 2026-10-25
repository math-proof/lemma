import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.CechSectionsOfDivisor
import Lemma.Int.P2MUtil


/--
[AlgebraicCurve_exists_linearEquiv_cechH1_swap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_cechH1_swap.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F]
  {S S' : Set (AlgebraicCurve.Place K F)}
  {D : AlgebraicCurve.Divisor K F} :
-- imply
  ∃ e : AlgebraicCurve.cechH1 S S' D ≃ₗ[K] AlgebraicCurve.cechH1 S' S D,
      ∀ (f : F) (h : f ∈ AlgebraicCurve.lSpaceOn (S ∩ S') D) (h' : f ∈ AlgebraicCurve.lSpaceOn (S' ∩ S) D),
        e (Submodule.Quotient.mk ⟨f, h⟩) = Submodule.Quotient.mk ⟨f, h'⟩ := by
  have hinter : AlgebraicCurve.lSpaceOn (S ∩ S') D = AlgebraicCurve.lSpaceOn (S' ∩ S) D := by rw [Set.inter_comm]
  let e₀ : ↥(AlgebraicCurve.lSpaceOn (S ∩ S') D) ≃ₗ[K] ↥(AlgebraicCurve.lSpaceOn (S' ∩ S) D) := LinearEquiv.ofEq _ _ hinter
  have he₀ : ∀ g : ↥(AlgebraicCurve.lSpaceOn (S ∩ S') D), ((e₀ g : ↥(AlgebraicCurve.lSpaceOn (S' ∩ S) D)) : F) = g :=
    fun g => rfl
  have hmap : (LinearMap.range (AlgebraicCurve.cechDiff S S' D)).map (e₀ : _ →ₗ[K] _) =
      LinearMap.range (AlgebraicCurve.cechDiff S' S D) := by
-- proof
    ext g
    rw [AlgebraicCurve.mem_range_cechDiff_iff, Submodule.mem_map]
    constructor
    ·
      rintro ⟨g', hg', rfl⟩
      rw [LinearEquiv.coe_coe, he₀, sup_comm]
      exact (AlgebraicCurve.mem_range_cechDiff_iff g').mp hg'
    ·
      intro hg
      refine ⟨e₀.symm g, ?_, by simp⟩
      rwa [AlgebraicCurve.mem_range_cechDiff_iff, sup_comm]
  refine ⟨Submodule.Quotient.equiv _ _ e₀ hmap, fun f h h' => ?_⟩
  rw [Submodule.Quotient.equiv_apply]
  rfl


-- created on 2026-10-23
