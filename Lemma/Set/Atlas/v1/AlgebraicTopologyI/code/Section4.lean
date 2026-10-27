import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section4
open AlgebraicTopologyI
open CategoryTheory


namespace AlgebraicTopologyI

/--
[functor_map_isSplitEpi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section4.lean)
-/
@[path]
lemma functor_map_isSplitEpi
  {C : Type u}
  [Category.{v} C]
  {D : Type u₂}
  [Category.{v₂} D]
  {F : C ⥤ D}
  {X Y : C}
  {f : X ⟶ Y}
  [IsSplitEpi f] :
-- imply
  IsSplitEpi (F.map f) :=
-- proof
  inferInstance

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[functor_map_isSplitMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section4.lean)
-/
@[path]
lemma functor_map_isSplitMono
  {C : Type u}
  [Category.{v} C]
  {D : Type u₂}
  [Category.{v₂} D]
  {F : C ⥤ D}
  {X Y : C}
  {f : X ⟶ Y}
  [IsSplitMono f] :
-- imply
  IsSplitMono (F.map f) :=
-- proof
  inferInstance

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[functor_preserves_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section4.lean)
-/
@[path]
lemma functor_preserves_split
  {C : Type u}
  [Category.{v} C]
  {D : Type u₂}
  [Category.{v₂} D]
  {F : C ⥤ D}
  {X Y : C}
  {f : X ⟶ Y} :
-- imply
  (IsSplitEpi f → IsSplitEpi (F.map f)) ∧ (IsSplitMono f → IsSplitMono (F.map f)) :=
-- proof
  ⟨fun _ => functor_map_isSplitEpi F f, fun _ => functor_map_isSplitMono F f⟩

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[isIso_iff_isSplitEpi_and_isSplitMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section4.lean)
-/
@[path]
lemma isIso_iff_isSplitEpi_and_isSplitMono
  {C : Type u}
  [Category.{v} C]
  {X Y : C}
  {f : X ⟶ Y} :
-- imply
  IsIso f ↔ IsSplitEpi f ∧ IsSplitMono f := by
-- proof
  constructor
  · intro h
    exact ⟨IsSplitEpi.of_iso f, IsSplitMono.of_iso f⟩
  · rintro ⟨hse, hsm⟩
    haveI := hse
    haveI := hsm
    exact isIso_of_mono_of_isSplitEpi f

end AlgebraicTopologyI


-- created on 2026-10-23
