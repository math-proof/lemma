/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ConductorIdeal.lean -/

module

public import Def.RingTheory.ConductorIdeal
public import Theorem.Int.ConductorIdeal
public import Theorem.MathlibExtTest.RingTheory.ConductorIdeal

@[expose] public section

/-- The diagonal subalgebra of `ℤ × ℤ`. -/
def diagSubalgebra : Subalgebra ℤ (ℤ × ℤ) where
  carrier := {p | p.1 = p.2}
  mul_mem' ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul] at ha hb ⊢
    rw [ha, hb]
  add_mem' ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at ha hb ⊢
    rw [ha, hb]
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq, Prod.algebraMap_apply]

