import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.EffaceableUniversal
open CategoryTheory CategoryTheory.Limits DerivedFunctorsDefs


namespace DerivedFunctorsDefs

/--
[CohomDeltaFunctor.IsEffaceable.toIsEffaceableMorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma CohomDeltaFunctor.IsEffaceable.toIsEffaceableMorphism
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D}
-- given
  (hF : F.IsEffaceable) :
-- imply
  F.IsEffaceableMorphism := by
-- proof
  intro n X
  obtain ⟨I, i, hi_mono, hI_zero⟩ := hF n X
  exact ⟨I, i, hi_mono, hI_zero.eq_of_tgt _ _⟩

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[CohomDeltaFunctor.IsEffaceableMorphism.toPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma CohomDeltaFunctor.IsEffaceableMorphism.toPointwise
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D}
-- given
  (hF : F.IsEffaceableMorphism) :
-- imply
  F.IsEffaceablePointwise := by
-- proof
  intro n X Y m
  obtain ⟨N, φ, hφ_mono, hφ_map⟩ := hF n X
  exact ⟨N, φ, hφ_mono, by rw [hφ_map, comp_zero]⟩

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[CohomDeltaFunctor.IsEffaceablePointwise.toMorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma CohomDeltaFunctor.IsEffaceablePointwise.toMorphism
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D}
-- given
  (hF : F.IsEffaceablePointwise) :
-- imply
  F.IsEffaceableMorphism := by
-- proof
  intro n X
  obtain ⟨N, φ, hφ_mono, hφ_eq⟩ := hF n X _ (𝟙 ((F.T (n + 1)).obj X))
  exact ⟨N, φ, hφ_mono, by rwa [Category.id_comp] at hφ_eq⟩

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[CohomDeltaFunctor.IsEffaceable.toPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma CohomDeltaFunctor.IsEffaceable.toPointwise
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D}
-- given
  (hF : F.IsEffaceable) :
-- imply
  F.IsEffaceablePointwise :=
-- proof
  hF.toIsEffaceableMorphism.toPointwise

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[CohomDeltaFunctor.isEffaceableMorphism_iff_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma CohomDeltaFunctor.isEffaceableMorphism_iff_pointwise
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D} :
-- imply
  F.IsEffaceableMorphism ↔ F.IsEffaceablePointwise :=
-- proof
  ⟨CohomDeltaFunctor.IsEffaceableMorphism.toPointwise,
    CohomDeltaFunctor.IsEffaceablePointwise.toMorphism⟩

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[delta_epi_of_map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma delta_epi_of_map_zero
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D}
  {n : ℕ}
  {S : ShortComplex C}
-- given
  (hS : S.ShortExact)
  (hf : (F.T (n + 1)).map S.f = 0) :
-- imply
  Epi (F.δ n S hS) :=
-- proof
  (F.exact_left n S hS).epi_f hf

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[delta_epi_of_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma delta_epi_of_vanishing
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D}
  {n : ℕ}
  {S : ShortComplex C}
-- given
  (hS : S.ShortExact)
  (hI : IsZero ((F.T (n + 1)).obj S.X₂)) :
-- imply
  Epi (F.δ n S hS) :=
-- proof
  (F.exact_left n S hS).epi_f (hI.eq_of_tgt _ _)

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[effaceable_morphism_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma effaceable_morphism_unique
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F G : CohomDeltaFunctor C D}
  {m₁ m₂ : F.Morphism G}
-- given
  (hF : F.IsEffaceable)
  (h₀ : m₁.η 0 = m₂.η 0) :
-- imply
  ∀ n, m₁.η n = m₂.η n := by
-- proof
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    apply NatTrans.ext
    funext X
    obtain ⟨I, i, hi_mono, hI_zero⟩ := hF n X
    haveI : Mono i := hi_mono
    let S : ShortComplex C := ShortComplex.cokernelSequence i
    have hSE : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
        (show Mono i from inferInstance) (show Epi (cokernel.π i) from inferInstance)
    have hδ_epi : Epi (F.δ n S hSE) := delta_epi_of_vanishing n S hSE hI_zero
    have h1 := m₁.comm_δ n S hSE
    have h2 := m₂.comm_δ n S hSE
    rw [show (m₁.η n).app S.X₃ = (m₂.η n).app S.X₃ from congr_fun
      (congr_arg NatTrans.app ih) S.X₃] at h1
    have hrhs : F.δ n S hSE ≫ (m₁.η (n + 1)).app S.X₁ =
      F.δ n S hSE ≫ (m₂.η (n + 1)).app S.X₁ := by rw [← h1, ← h2]
    exact (cancel_epi (F.δ n S hSE)).mp hrhs

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[effaceable_morphism_unique_of_effaceableMorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma effaceable_morphism_unique_of_effaceableMorphism
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F G : CohomDeltaFunctor C D}
  {m₁ m₂ : F.Morphism G}
-- given
  (hF : F.IsEffaceableMorphism)
  (h₀ : m₁.η 0 = m₂.η 0) :
-- imply
  ∀ n, m₁.η n = m₂.η n := by
-- proof
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    apply NatTrans.ext
    funext X
    obtain ⟨I, i, hi_mono, hI_map⟩ := hF n X
    haveI : Mono i := hi_mono
    let S : ShortComplex C := ShortComplex.cokernelSequence i
    have hSE : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
        (show Mono i from inferInstance) (show Epi (cokernel.π i) from inferInstance)
    have hδ_epi : Epi (F.δ n S hSE) := delta_epi_of_map_zero n S hSE hI_map
    have h1 := m₁.comm_δ n S hSE
    have h2 := m₂.comm_δ n S hSE
    rw [show (m₁.η n).app S.X₃ = (m₂.η n).app S.X₃ from congr_fun
      (congr_arg NatTrans.app ih) S.X₃] at h1
    have hrhs : F.δ n S hSE ≫ (m₁.η (n + 1)).app S.X₁ =
      F.δ n S hSE ≫ (m₂.η (n + 1)).app S.X₁ := by rw [← h1, ← h2]
    exact (cancel_epi (F.δ n S hSE)).mp hrhs

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[effaceable_morphism_unique_of_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma effaceable_morphism_unique_of_pointwise
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F G : CohomDeltaFunctor C D}
  {m₁ m₂ : F.Morphism G}
-- given
  (hF : F.IsEffaceablePointwise)
  (h₀ : m₁.η 0 = m₂.η 0) :
-- imply
  ∀ n, m₁.η n = m₂.η n :=
-- proof
  effaceable_morphism_unique_of_effaceableMorphism F G hF.toMorphism m₁ m₂ h₀

end DerivedFunctorsDefs

namespace DerivedFunctorsDefs

/--
[effaceable_step_zero_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean)
-/
@[path]
lemma effaceable_step_zero_condition
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F G : CohomDeltaFunctor C D}
  {n : ℕ}
  {X : C}
  {I : C}
  {i : X ⟶ I}
  [Mono i]
  {η_n : F.T n ⟶ G.T n}
-- given
  (_hI_map : (F.T (n + 1)).map i = 0) :
-- imply
  let S := ShortComplex.cokernelSequence i let hSE := ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i) (show Mono i from inferInstance) (show Epi (cokernel.π i) from inferInstance) (F.T n).map S.g ≫ (η_n.app S.X₃ ≫ G.δ n S hSE) = 0 := by
-- proof
  simp only
  rw [← Category.assoc, η_n.naturality]
  rw [Category.assoc]
  rw [G.comp_δ_zero, comp_zero]
/-- Inductive construction (as a raw family of natural transformations) of a
morphism of δ-functors extending a given degree-zero component. -/

end DerivedFunctorsDefs


-- created on 2026-10-23
