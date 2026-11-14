import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Topology


@[path]
private lemma main
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
  [Algebra R S]
-- given
  (hcont : Continuous (algebraMap R S))
  (hopen : IsOpenMap (algebraMap R S)) :
-- imply
  IsModuleTopology R S := by
-- proof
  refine ⟨?_⟩
  have : ContinuousSMul R S := continuousSMul_of_algebraMap R S hcont
  have hcont_id : Continuous[moduleTopology R S, _] id :=
    continuous_id_iff_le.2 <| moduleTopology_le _ _
  have hcont_alg : Continuous[_, moduleTopology R S] (Algebra.linearMap R S) :=
    let := moduleTopology R S
    let : ContinuousAdd S := ModuleTopology.continuousAdd _ _
    let : ContinuousSMul R S := ModuleTopology.continuousSMul _ _
    IsModuleTopology.continuous_of_linearMap _
  have hopen_mpr {U : Set S} (h : IsOpen U) : IsOpen[moduleTopology R S] U :=
    @Continuous.isOpen_preimage S S (moduleTopology R S) _ id hcont_id U h
  have hopen_mp {U : Set S} (h : IsOpen[moduleTopology R S] U)
    (hUS : U ⊆ Set.range (algebraMap R S)) : IsOpen U :=
    Set.image_preimage_eq_of_subset hUS ▸ hopen _ <|
      @Continuous.isOpen_preimage R S _ (moduleTopology R S) _ hcont_alg U h
  rw [IsTopologicalRing.isTopologicalAddGroup.ext_iff <|
    @IsModuleTopology.isTopologicalAddGroup R _ _ S _ _ (moduleTopology R S)
      (@IsModuleTopology.mk R _ S _ _ (moduleTopology R S) rfl)]
  apply (nhds_basis_opens 0).ext (@nhds_basis_opens S (moduleTopology R S) 0)
  ·
    intro U hU
    refine ⟨U, ⟨⟨hU.1, hopen_mpr hU.2⟩, ?_⟩⟩
    simp
  ·
    intro U hU
    refine ⟨Set.range (algebraMap R S) ∩ U, ⟨⟨⟨⟨0, by simp⟩, hU.1⟩, ?_⟩, by simp⟩⟩
    apply hopen_mp (@IsOpen.inter _ (moduleTopology R S) _ _
      (hopen_mpr hopen.isOpen_range) hU.2)
    simp


-- created on 2026-11-13
