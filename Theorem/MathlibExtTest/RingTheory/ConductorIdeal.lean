/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ConductorIdeal.lean -/


import Def.RingTheory.ConductorIdeal
import Lemma.Int.ConductorIdeal


-- Conductor of the top subalgebra.
example : (⊤ : Subalgebra ℤ ℤ).conductorIdeal = ⊤ :=
  Subalgebra.conductorIdeal_top

-- Monogenic specialization recovers Mathlib's element-generated conductor.
example (x : ℤ) :
    (Algebra.adjoin ℤ ({x} : Set ℤ)).conductorIdeal = conductor ℤ x :=
  Subalgebra.adjoin_conductorIdeal x

-- Universal property for an arbitrary ideal.
example (A : Subalgebra ℤ ℤ) (I : Ideal ℤ) (h : (I : Set ℤ) ⊆ (A : Set ℤ)) :
    I ≤ A.conductorIdeal :=
  Subalgebra.le_conductorIdeal_iff.mpr h

