import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.IsFiniteTypeOfCoversTop
open CategoryTheory Limits SheafOfModules


/--
[QuasicoherentData.bind_isFinitePresentation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IsFiniteTypeOfCoversTop.lean)
-/
@[path]
lemma QuasicoherentData.bind_isFinitePresentation
  {C : Type u}
  [Category.{u} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{u} R}
  {I : Type u}
  {X : I → C}
  {D : Π i, QuasicoherentData (M.over (X i))}
-- given
  (hX : J.CoversTop X)
  (hD : ∀ i, (D i).IsFinitePresentation) :
-- imply
  (QuasicoherentData.bind M X hX D).IsFinitePresentation where isFinite_presentation ij :=
-- proof
  {
    isFiniteType_generators := {
      finite := by
        simp only [QuasicoherentData.bind, Presentation.of_isIso_generators,
          GeneratingSections.ofEpi_I, Presentation.map_generators_I]
        exact ((hD ij.1).isFinite_presentation ij.2).isFiniteType_generators.finite
    }
    finite_relations := by
      have := ((hD ij.1).isFinite_presentation ij.2).finite_relations
      rw [show ((QuasicoherentData.bind M X hX D).presentation ij).relations.I =
        ((D ij.1).presentation ij.2).relations.I from by
        simp only [QuasicoherentData.bind, Presentation.of_isIso,
          GeneratingSections.ofEpi_I, Presentation.map_relations_I]]
      exact this
    }

/--
[QuasicoherentData.bind_localGeneratorsData_isFiniteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IsFiniteTypeOfCoversTop.lean)
-/
@[path]
lemma QuasicoherentData.bind_localGeneratorsData_isFiniteType
  {C : Type u}
  [Category.{u} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{u} R}
  {I : Type u}
  {X : I → C}
  {D : Π i, QuasicoherentData (M.over (X i))}
-- given
  (hX : J.CoversTop X)
  (hD : ∀ (i : I) (j : (D i).I), ((D i).presentation j).generators.IsFiniteType) :
-- imply
  (QuasicoherentData.bind M X hX D).localGeneratorsData.IsFiniteType where isFiniteType ij :=
-- proof
  {
    finite := by
      simp only [QuasicoherentData.localGeneratorsData_generators]
      have h := (hD ij.1 ij.2).finite
      rw [show ((QuasicoherentData.bind M X hX D).presentation ij).generators.I =
        ((D ij.1).presentation ij.2).generators.I from by
        simp only [QuasicoherentData.bind, Presentation.of_isIso_generators,
          GeneratingSections.ofEpi_I, Presentation.map_generators_I]]
      exact h }

/--
[IsFinitePresentation.of_coversTop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IsFiniteTypeOfCoversTop.lean)
-/
@[path]
lemma IsFinitePresentation.of_coversTop
  {C : Type u}
  [Category.{u} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{u} R}
  {I : Type u}
  {X : I → C}
  [∀ i, IsFinitePresentation (M.over (X i))]
-- given
  (hX : J.CoversTop X) :
-- imply
  IsFinitePresentation M where exists_quasicoherentData := by
-- proof
  have h : ∀ i, ∃ (q : QuasicoherentData (M.over (X i))), q.IsFinitePresentation :=
    fun i => IsFinitePresentation.exists_quasicoherentData (M.over (X i))
  choose D hD using h
  exact ⟨QuasicoherentData.bind M X hX D,
    QuasicoherentData.bind_isFinitePresentation M X hX D hD⟩

/--
[IsFiniteType.of_coversTop_of_isFinitePresentation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IsFiniteTypeOfCoversTop.lean)
-/
@[path]
lemma IsFiniteType.of_coversTop_of_isFinitePresentation
  {C : Type u}
  [Category.{u} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{u} R}
  {I : Type u}
  {X : I → C}
  [∀ i, IsFinitePresentation (M.over (X i))]
-- given
  (hX : J.CoversTop X) :
-- imply
  IsFiniteType M := by
-- proof
  have := IsFinitePresentation.of_coversTop M X hX
  infer_instance

/--
[IsFiniteType.of_coversTop_of_isFinitePresentation'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IsFiniteTypeOfCoversTop.lean)
-/
@[path]
lemma IsFiniteType.of_coversTop_of_isFinitePresentation'
  {C : Type u}
  [Category.{u} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{u} R}
  {I : Type u}
  {X : I → C}
-- given
  (hX : J.CoversTop X)
  (hFP : ∀ i, IsFinitePresentation (M.over (X i))) :
-- imply
  IsFiniteType M := by
-- proof
  haveI : ∀ i, IsFinitePresentation (M.over (X i)) := hFP
  exact IsFiniteType.of_coversTop_of_isFinitePresentation M X hX


-- created on 2026-10-23
