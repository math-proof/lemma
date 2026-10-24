import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[faultfree_tilings_height2_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  FaultfreeTilingsHeight2.IsFiniteType := by
-- proof
  intro m
  have h := tilingsHeight2_isFiniteType m
  -- The faultfree tilings embed into all tilings
  let f : (Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T}) →
          (Σ n : ℕ, Tiling (Rectangle n 2)) := fun ⟨n, T, _⟩ => ⟨n, T⟩
  have hinj : Function.Injective f := by
    intro ⟨n₁, T₁, h₁⟩ ⟨n₂, T₂, h₂⟩ heq
    have heq' := Sigma.mk.inj_iff.mp heq
    obtain ⟨hn, hT⟩ := heq'
    subst hn
    simp only [heq_eq_eq] at hT
    subst hT
    rfl
  -- The image of the faultfree tilings under f is a subset of all tilings
  have himg : f '' {a | FaultfreeTilingsHeight2.weight a = m} ⊆
              {a | TilingsHeight2.weight a = m} := by
    intro ⟨n, T⟩ ⟨⟨n', T', hT'⟩, hmem, heq⟩
    simp only [Set.mem_ofPred_eq] at hmem ⊢
    obtain ⟨hn, hTeq⟩ := Sigma.mk.inj_iff.mp heq
    subst hn
    simp only [heq_eq_eq] at hTeq
    subst hTeq
    exact hmem
  -- Since the image is a subset of a finite set, it's finite
  have himg_fin : (f '' {a | FaultfreeTilingsHeight2.weight a = m}).Finite := h.subset himg
  -- Use Set.Finite.of_finite_image with InjOn
  have hinjOn : Set.InjOn f {a | FaultfreeTilingsHeight2.weight a = m} :=
    fun _ _ _ _ h => hinj h
  exact Set.Finite.of_finite_image himg_fin hinjOn


-- created on 2026-10-20
