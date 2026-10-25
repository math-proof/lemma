/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ConductorIdeal.lean -/


import Def.RingTheory.ConductorIdeal
import Lemma.Int.ConductorIdeal
import Def.MathlibExtTest.RingTheory.ConductorIdeal


-- The diagonal subalgebra of `ℤ × ℤ` has bottom conductor.
example : diagSubalgebra.conductorIdeal = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  have hp' : ∀ t : ℤ × ℤ, (p * t).1 = (p * t).2 := fun t =>
    mem_diagSubalgebra.mp (Subalgebra.mem_conductorIdeal.mp hp t)
  have h1 := hp' (1, 0)
  have h2 := hp' (0, 1)
  simp only [Prod.fst_mul, Prod.snd_mul, mul_one, mul_zero] at h1 h2
  exact (Submodule.mem_bot _).mpr (Prod.ext h1 h2.symm)

-- Finiteness characterization for overrings of `ℤ` in `ℚ`.
example (T : Subalgebra ℤ ℚ) :
    (⊥ : Subalgebra ℤ ↥T).conductorIdeal ≠ ⊥ ↔ Module.Finite ℤ ↥T :=
  Subalgebra.bot_conductorIdeal_ne_bot_iff T

-- Nonzero conductor forces finiteness.
example (T : Subalgebra ℤ ℚ)
    (h : (⊥ : Subalgebra ℤ ↥T).conductorIdeal ≠ ⊥) : Module.Finite ℤ ↥T :=
  Subalgebra.finite_of_conductorIdeal_bot_ne_bot T h

-- The characterization for the integral closure of `ℤ` in `ℚ`.
example :
    (⊥ : Subalgebra ℤ ↥(integralClosure ℤ ℚ)).conductorIdeal ≠ ⊥ ↔
      Module.Finite ℤ ↥(integralClosure ℤ ℚ) :=
  Subalgebra.integralClosure_bot_conductorIdeal_ne_bot_iff

#print axioms Subalgebra.bot_conductorIdeal_ne_bot_iff
#print axioms Subalgebra.integralClosure_bot_conductorIdeal_ne_bot_iff

