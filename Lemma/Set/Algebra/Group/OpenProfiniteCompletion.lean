import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Topology.Algebra.Group.OpenProfiniteCompletion.Part2
open CategoryTheory
open scoped Pointwise
open ProfiniteGrp.OpenProfiniteCompletion


namespace ProfiniteGrp.OpenProfiniteCompletion

/--
[etaFn_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
lemma etaFn_apply
  {G : Type u} [Group G] [TopologicalSpace G]
  {x : G}
  {H : Index G} :
-- imply
  ((etaFn G x).val H : G ⧸ H.1.toSubgroup) =
    QuotientGroup.mk x :=
-- proof
  rfl

end ProfiniteGrp.OpenProfiniteCompletion

namespace ProfiniteGrp.OpenProfiniteCompletion

/--
[denseRange_etaFn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
lemma denseRange_etaFn
  {G : Type u} [Group G] [TopologicalSpace G] :
-- imply
  DenseRange (etaFn G) := by
-- proof
  unfold etaFn completion
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv, Set.mem_preimage] at uDefaultSpec
  obtain ⟨J, _fJ, hJ1, hJ2⟩ := (isOpen_pi_iff.mp hsO) _ uDefaultSpec
  let M : Subgroup G := iInf fun (j : J) ↦ j.1.1.toSubgroup
  have hMNormal : M.Normal :=
    Subgroup.normal_iInf_normal fun _ ↦ inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  have hMOpen : IsOpen (M : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j ↦ j.1.2
  let m : Index G := ⟨{
    toSubgroup := M
    isNormal' := hMNormal
    isFiniteIndex' := hMFinite }, hMOpen⟩
  obtain ⟨origin, horigin⟩ := QuotientGroup.mk'_surjective M (spc m)
  use ⟨fun _ ↦ QuotientGroup.mk origin, fun _ _ _ ↦ rfl⟩
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a :=
    (iInf_le (fun (j : J) ↦ j.1.1.toSubgroup) ⟨a, a_in_J⟩).hom
  rw [← (⟨fun _ ↦ QuotientGroup.mk origin, fun _ _ _ ↦ rfl⟩ :
    ProfiniteGrp.limit (diagram G)).property M_to_Na]
  change (finiteGrpDiagram G).map M_to_Na (QuotientGroup.mk' M origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

end ProfiniteGrp.OpenProfiniteCompletion

namespace ProfiniteGrp.OpenProfiniteCompletion

/--
[denseRange_eta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
lemma denseRange_eta
  {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :
-- imply
  DenseRange (eta G) :=
-- proof
  denseRange_etaFn G

end ProfiniteGrp.OpenProfiniteCompletion

/--
[etaFn_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
private lemma etaFn_continuous_eq
  {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :
-- imply
  Continuous (etaFn G) := by
-- proof
  apply ProfiniteGrp.OpenProfiniteCompletion.etaFn_continuous G


-- created on 2026-10-20
-- updated on 2026-10-26
