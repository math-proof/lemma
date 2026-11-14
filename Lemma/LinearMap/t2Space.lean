import Mathlib
import Initialize.Tactic.Attr.Basic
open IsModuleTopology


@[path]
private lemma main
  [Semiring R]
  [AddCommGroup M]
  [Module R M]
  [Module.Free R M]
  [TopologicalSpace R]
  [TopologicalSpace M]
  [T2Space R]
  [ContinuousAdd R]
  [ContinuousMul R]
  [IsModuleTopology R M] :
-- imply
  T2Space M := by
-- proof
  have := IsModuleTopology.isTopologicalAddGroup R M
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  let f := (Module.Free.chooseBasis R M).repr |>.toLinearMap
  let g : LinearMap (RingHom.id R) (Finsupp (Module.Free.ChooseBasisIndex R M) R)
    (Module.Free.ChooseBasisIndex R M → R) := {
    __ := Finsupp.coeFnAddHom
    map_smul' _ _ := rfl
  }
  suffices hpre : (g.comp f) ⁻¹' {0} = {0} by
    rw [← hpre]
    apply IsClosed.preimage <| IsModuleTopology.continuous_of_linearMap (g.comp f)
    apply isClosed_singleton
  ext x
  simp [map_eq_zero_iff g DFunLike.coe_injective,
    map_eq_zero_iff f (Module.Free.chooseBasis R M).repr.injective]


-- created on 2026-11-13
