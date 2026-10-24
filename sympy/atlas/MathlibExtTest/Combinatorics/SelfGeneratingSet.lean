/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SelfGeneratingSet.lean -/


import sympy.atlas.Combinatorics.SelfGeneratingSet
import Lemma.Finset.SelfGeneratingSet


open scoped Classical

namespace MetaMathlibExt.SelfGeneratingSet

example : (0 : Nat) ∈ GeneratedSet {fun n => n + 1} 0 :=
  Gen.seed_mem

example : (1 : Nat) ∈ GeneratedSet {fun n => n + 1} 0 := by
  have h0 : Gen {fun n => n + 1} 0 0 := Gen.seed_mem
  exact Gen.step 0 h0 (fun n => n + 1) (Finset.mem_singleton_self _)

example : (3 : Nat) ∈ GeneratedSet {fun n => n + 1} 0 := by
  have h0 : Gen {fun n => n + 1} 0 0 := Gen.seed_mem
  have h1 := Gen.step 0 h0 (fun n => n + 1) (Finset.mem_singleton_self _)
  have h2 := Gen.step _ h1 (fun n => n + 1) (Finset.mem_singleton_self _)
  exact Gen.step _ h2 (fun n => n + 1) (Finset.mem_singleton_self _)

example : SG {fun n => n + 1} 0 (GeneratedSet {fun n => n + 1} 0) :=
  generated_isSG

example : FixedPoint {fun n => n + 1} 0 (GeneratedSet {fun n => n + 1} 0) :=
  generated_fixedPoint

example (C : Set Nat) (hC : FixedPoint {fun n => n + 1} 0 C) :
    C = GeneratedSet {fun n => n + 1} 0 :=
  fixedPoint_eq_generated succ_strictGrowth hC

end MetaMathlibExt.SelfGeneratingSet
