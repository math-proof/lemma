import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.CurveMorphisms
open AlgebraicGeometry CategoryTheory TopologicalSpace Order Set


/--
[SmoothProjectiveCurve.morphism_isClosedMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveMorphisms.lean)
-/
@[path]
lemma SmoothProjectiveCurve.morphism_isClosedMap
  {C : Scheme}
  [SmoothProjectiveCurve C]
  {Y : Scheme}
  {f : C ⟶ Y} :
-- imply
  IsClosedMap f.base := by
-- proof
  haveI := morphism_universallyClosed f
  exact Scheme.Hom.isClosedMap f

/--
[irreducible_closed_eq_univ_of_not_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveMorphisms.lean)
-/
@[path]
lemma irreducible_closed_eq_univ_of_not_subsingleton
  [TopologicalSpace Y]
  [T0Space Y]
  [IrreducibleSpace Y]
  {S : Set Y}
-- given
  (hdim : topologicalKrullDim Y ≤ 1)
  (hS_irred : IsIrreducible S)
  (hS_closed : IsClosed S)
  (hS_not_sub : ¬ S.Subsingleton) :
-- imply
  S = Set.univ := by
-- proof
  by_contra hS_ne_univ
  rw [Set.not_subsingleton_iff] at hS_not_sub
  obtain ⟨x, hx, y, hy, hne⟩ := hS_not_sub
  suffices ∃ z, z ∈ S ∧ closure ({z} : Set Y) ⊂ S by
    obtain ⟨z, _, hcz_ssubset_S⟩ := this
    let a : IrreducibleCloseds Y :=
      ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    let b : IrreducibleCloseds Y := ⟨S, hS_irred, hS_closed⟩
    let c : IrreducibleCloseds Y :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
    have hab : a < b := hcz_ssubset_S
    have hbc : b < c := ⟨subset_univ _, fun h' => hS_ne_univ (eq_univ_of_univ_subset h')⟩
    let s : LTSeries (IrreducibleCloseds Y) :=
      ⟨2, ![a, b, c], fun i => by fin_cases i <;> simpa⟩
    exact absurd (le_trans s.length_le_krullDim hdim) (by norm_num)
  by_contra hall
  simp only [not_exists, not_and] at hall
  have hcl_eq : ∀ z ∈ S, closure ({z} : Set Y) = S := by
    intro z hz
    have hle : closure ({z} : Set Y) ⊆ S :=
      closure_minimal (singleton_subset_iff.mpr hz) hS_closed
    exact le_antisymm hle (by
      by_contra h
      exact hall z hz ⟨hle, h⟩)
  exact hne (Inseparable.eq ((inseparable_iff_closure_eq).mpr
    ((hcl_eq x hx).trans (hcl_eq y hy).symm)))

/--
[SmoothProjectiveCurve.morphism_constant_or_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveMorphisms.lean)
-/
@[path]
lemma SmoothProjectiveCurve.morphism_constant_or_surjective
  {C₁ C₂ : Scheme}
  [SmoothProjectiveCurve C₁]
  [SmoothProjectiveCurve C₂]
  {φ : C₁ ⟶ C₂} :
-- imply
  IsConstantMorphism φ ∨ Function.Surjective φ.base := by
-- proof
  by_cases h : (range φ.base).Subsingleton
  ·
    left
    obtain ⟨x₀⟩ := SmoothProjectiveCurve.nonempty (C := C₁)
    exact ⟨φ.base x₀, fun x => h ⟨x, rfl⟩ ⟨x₀, rfl⟩⟩
  ·
    right
    have hclosed_range : IsClosed (range φ.base) := by
      rw [← image_univ]
      exact SmoothProjectiveCurve.morphism_isClosedMap φ _ isClosed_univ
    have hirred_range : IsIrreducible (range φ.base) := by
      rw [← image_univ]
      exact (IrreducibleSpace.isIrreducible_univ C₁).image φ.base
        (Scheme.Hom.continuous φ).continuousOn
    have hdim : topologicalKrullDim C₂ ≤ 1 := le_of_eq krullDim_eq
    have hrange_eq : range φ.base = Set.univ :=
      irreducible_closed_eq_univ_of_not_subsingleton hdim hirred_range hclosed_range h
    exact fun y => by rw [← mem_range]; simp [hrange_eq]

/--
[SmoothProjectiveCurve.rationalMap_constant_or_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveMorphisms.lean)
-/
@[path]
lemma SmoothProjectiveCurve.rationalMap_constant_or_surjective
  {C₁ C₂ : Scheme}
  [SmoothProjectiveCurve C₁]
  [SmoothProjectiveCurve C₂]
  {φ : C₁ ⤏ C₂}
  {f : C₁ ⟶ C₂}
-- given
  (_hf : f.toRationalMap = φ) :
-- imply
  IsConstantMorphism f ∨ Function.Surjective f.base :=
-- proof
  morphism_constant_or_surjective f
/-- (Corollary 18.7) The unique morphism extending a rational map between smooth projective curves is either constant or surjective. -/


-- created on 2026-10-23
