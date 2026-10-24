/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import sympy.atlas.Topology.InverseLimit
import Lemma.Set.InverseLimit


/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/

namespace InverseLimitTest

/-- Identity transition maps on the constant `Bool` family over `Fin 2`. -/
private def boolId : ∀ ⦃i j : Fin 2⦄, i ≤ j → Bool → Bool := fun {_ _} _ => id

/-- The constant `true` tuple is compatible. -/
private def constTrue : Fin 2 → Bool := fun _ => true

example : constTrue ∈ InverseLimit.carrier boolId := by
  intro i j _
  rfl

example : (fun _ : Fin 2 => false) ∈ InverseLimit.carrier boolId := by
  intro i j _
  rfl

/-- A non-constant tuple over `Fin 2` violates compatibility at `0 ≤ 1`. -/
private def mixed : Fin 2 → Bool := ![true, false]

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

/-- Singleton index: every tuple is compatible with the identity transition map. -/
private def unitId : ∀ ⦃i j : Unit⦄, i ≤ j → Bool → Bool := fun {_ _} _ => id

example (x : Unit → Bool) : x ∈ InverseLimit.carrier unitId := by
  intro i j _
  cases i
  cases j
  rfl

/-- Constant `Fin 3` family with identity maps: diagonal tuples are limits. -/
private def finId : ∀ ⦃i j : Fin 2⦄, i ≤ j → Fin 3 → Fin 3 := fun {_ _} _ => id

example (a : Fin 3) : (fun _ : Fin 2 => a) ∈ InverseLimit.carrier finId := by
  intro i j _
  rfl

example : IsCompact (InverseLimit.carrier finId) := by
  apply InverseLimit.isCompact_carrier (f := finId)
  intro i j _
  exact continuous_id

end InverseLimitTest
