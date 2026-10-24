import Mathlib
import sympy.Basic
import sympy.atlas.Topology.MetricSpace.LipschitzParametrizable
open Finset
open Set


/--
[unitCube_zero_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
lemma unitCube_zero_mem
  {d : ℕ} :
-- imply
  (0 : Fin d → ℝ) ∈ unitCube d :=
-- proof
  Set.mem_Icc.mpr ⟨le_rfl, fun _ => zero_le_one⟩

/--
[isLipschitzParametrizable_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
lemma isLipschitzParametrizable_empty
  [MetricSpace X]
  {d : ℕ} :
-- imply
  IsLipschitzParametrizable d (∅ : Set X) := by
-- proof
  refine ⟨0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  symm
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨i, _, _⟩ := hx
  exact i.elim0

/--
[isLipschitzParametrizable_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
lemma isLipschitzParametrizable_singleton
  [MetricSpace X]
  {d : ℕ}
  {x : X} :
-- imply
  IsLipschitzParametrizable d ({x} : Set X) := by
-- proof
  refine ⟨1, fun _ _ => x, fun _ => ⟨0, LipschitzWith.const' _⟩, ?_⟩
  ext y
  simp only [Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro rfl
    exact ⟨0, ⟨0, unitCube_zero_mem d⟩, rfl⟩
  · rintro ⟨_, _, rfl⟩
    rfl

namespace Finset

/--
[isLipschitzParametrizable_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
lemma isLipschitzParametrizable_coe
  [MetricSpace X]
  {d : ℕ}
  {s : Finset X} :
-- imply
  IsLipschitzParametrizable d (↑s : Set X) := by
-- proof
  refine ⟨Fintype.card ↥s, fun i _ => ((Fintype.equivFin ↥s).symm i : X),
    fun _ => ⟨0, LipschitzWith.const' _⟩, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · intro hx
    refine ⟨Fintype.equivFin ↥s ⟨x, hx⟩, ⟨0, unitCube_zero_mem d⟩, ?_⟩
    show ((Fintype.equivFin ↥s).symm (Fintype.equivFin ↥s ⟨x, hx⟩) : ↥s).val = x
    rw [Equiv.symm_apply_apply]
  · rintro ⟨i, _, rfl⟩
    exact ((Fintype.equivFin ↥s).symm i).property
end Finset


namespace Set

/--
[Finite.isLipschitzParametrizable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
lemma Finite.isLipschitzParametrizable
  [MetricSpace X]
  {B : Set X}
  {d : ℕ}
-- given
  (hB : B.Finite) :
-- imply
  IsLipschitzParametrizable d B := by
-- proof
  obtain ⟨s, rfl⟩ := hB.exists_finset_coe
  exact Finset.isLipschitzParametrizable_coe d s

end Set

/--
[IsLipschitzParametrizable.image_lipschitzWith](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
lemma IsLipschitzParametrizable.image_lipschitzWith
  [MetricSpace X] [MetricSpace Y]
  {d : ℕ}
  {B : Set X}
  {f : X → Y}
  {K : NNReal}
-- given
  (hB : IsLipschitzParametrizable d B)
  (hf : LipschitzWith K f) :
-- imply
  IsLipschitzParametrizable d (f '' B) := by
-- proof
  obtain ⟨n, charts, hLip, hEq⟩ := hB
  refine ⟨n, fun i => f ∘ charts i, fun i => ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hLip i
    exact ⟨K * L, hf.comp hL⟩
  · rw [hEq, Set.image_iUnion]
    refine Set.iUnion_congr fun i => ?_
    ext y
    simp only [Set.mem_image, Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨charts i a, ⟨a, rfl⟩, rfl⟩


-- created on 2026-10-20
-- updated on 2026-10-23
