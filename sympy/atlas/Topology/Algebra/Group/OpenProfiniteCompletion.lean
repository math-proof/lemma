/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean -/

import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# Open profinite completion from open finite-index normal subgroups.

Corrects the source formalization: an open subgroup of an arbitrary
topological group need not have finite index. We index by open *and*
finite-index normal subgroups.
-/

open CategoryTheory
open scoped Pointwise

universe u

namespace ProfiniteGrp.OpenProfiniteCompletion

/-- Open finite-index normal subgroups of `G`, the index category. -/
abbrev Index (G : Type u) [Group G] [TopologicalSpace G] :=
  { H : FiniteIndexNormalSubgroup G // IsOpen (H : Set G) }

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

/-- Continuity of `etaFn`; needs only separate continuity of `*`. -/
theorem etaFn_continuous (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : Continuous (etaFn G) := by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  apply Continuous.mk
  intro s _hs
  let s' : Set (G ⧸ H.1.toSubgroup) := fun x ↦ s x
  change IsOpen ((QuotientGroup.mk' H.1.toSubgroup) ⁻¹' s')
  rw [← (Set.biUnion_preimage_singleton (QuotientGroup.mk' H.1.toSubgroup) s')]
  refine isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ?_))
  convert! IsOpen.leftCoset H.2 (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  conv_lhs => rhs; rw [← QuotientGroup.out_eq' i]
  change (↑x : G ⧸ H.1.toSubgroup) = ↑(Quotient.out i) ↔
    x ∈ Quotient.out i • (↑H.1.toSubgroup : Set G)
  rw [eq_comm, QuotientGroup.eq]
  exact Iff.symm Set.mem_smul_set_iff_inv_smul_mem

/-- Canonical continuous monoid hom into the completion. -/
def eta (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : G →ₜ* completion G where
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := etaFn_continuous G
end ProfiniteGrp.OpenProfiniteCompletion
