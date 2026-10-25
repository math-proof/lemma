/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import Def.Topology.InverseLimit
import Lemma.Set.InverseLimit
import Def.MathlibExtTest.Topology.InverseLimit.Part2
/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

example : mixed ∉ InverseLimit.carrier boolId := by
  intro h
  have h01 := h (show (0 : Fin 2) ≤ 1 by decide)
  simp only [mixed, boolId, Matrix.cons_val_zero, Matrix.cons_val_one] at h01
  exact Bool.false_ne_true h01

/-- Membership unfolds to the compatibility condition. -/
example {x : Fin 2 → Bool} :
    x ∈ InverseLimit.carrier boolId ↔
      ∀ ⦃i j : Fin 2⦄ (h : i ≤ j), boolId h (x j) = x i :=
  InverseLimit.mem_carrier_iff

/-- Projection compatibility on a concrete compatible tuple. -/
example (h : (0 : Fin 2) ≤ 1) :
    boolId h (constTrue 1) = constTrue 0 :=
  InverseLimit.proj_compat (by intro i j _; rfl) h

/-- The limit set over the finite identity system is closed. -/
example : IsClosed (InverseLimit.carrier boolId) := by
  apply InverseLimit.isClosed_carrier (f := boolId)
  intro i j _
  exact continuous_id

/-- The limit set over the finite identity system is compact. -/
example : IsCompact (InverseLimit.carrier boolId) := by
  apply InverseLimit.isCompact_carrier (f := boolId)
  intro i j _
  exact continuous_id

end InverseLimitTest
