/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean -/

import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Abbrev.Topology.Algebra.Group.OpenProfiniteCompletion
open CategoryTheory
open scoped Pointwise

universe u

/-!
# Open profinite completion from open finite-index normal subgroups.

Corrects the source formalization: an open subgroup of an arbitrary
topological group need not have finite index. We index by open *and*
finite-index normal subgroups.
-/


namespace ProfiniteGrp.OpenProfiniteCompletion

/-- Finite-group diagram `G ⧸ H` with projection maps. -/
def finiteGrpDiagram (G : Type u) [Group G]
    [TopologicalSpace G] : Index G ⥤ FiniteGrp.{u} where
  obj H := FiniteGrp.of <| G ⧸ H.1.toSubgroup
  map f :=
    FiniteGrp.ofHom <| QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

/-- Profinite diagram obtained by forgetting to `ProfiniteGrp`. -/
def diagram (G : Type u) [Group G] [TopologicalSpace G] :
    Index G ⥤ ProfiniteGrp.{u} :=
  finiteGrpDiagram G ⋙ forget₂ (FiniteGrp.{u}) (ProfiniteGrp.{u})

/-- Open profinite completion as the limit of `diagram G`. -/
def completion (G : Type u) [Group G] [TopologicalSpace G] :
    ProfiniteGrp.{u} :=
  ProfiniteGrp.limit (diagram G)

/-- Canonical map `G → completion G` sending `x` to `(mk x)_H`. -/
def etaFn (G : Type u) [Group G] [TopologicalSpace G]
    (x : G) : completion G :=
  ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

end ProfiniteGrp.OpenProfiniteCompletion
