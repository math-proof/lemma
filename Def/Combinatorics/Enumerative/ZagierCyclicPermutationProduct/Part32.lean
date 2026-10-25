/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part34
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagAnchoredOrderEquivFullCycle (n : ℕ)
    (hn : 0 < n) :
    {e : Equiv.Perm (Fin n) // e (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩} ≃
      {s : Equiv.Perm (Fin n) // cycleQuotientCount s = 1} := by
  classical
  let z : Fin n := ⟨0, hn⟩
  let toCycle :
      {e : Equiv.Perm (Fin n) // e (zagBasePoint z) = zagBasePoint z} →
        {s : Equiv.Perm (Fin n) // cycleQuotientCount s = 1} := fun e =>
    ⟨zagHorizontal e.1, zagHorizontal_cycleCount e.1 hn⟩
  refine Equiv.ofBijective toCycle ?_
  constructor
  · intro e f hef
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have hhorizontal : zagHorizontal e.1 = zagHorizontal f.1 :=
      congrArg Subtype.val hef
    have hbase : zagBasePoint i = zagBasePoint z := Fin.ext rfl
    have hebase : e.1 (zagBasePoint i) = zagBasePoint i := by
      simpa only [hbase] using e.2
    have hfbase : f.1 (zagBasePoint i) = zagBasePoint i := by
      simpa only [hbase] using f.2
    calc
      e.1 i = (zagHorizontal e.1 ^ i.val) (e.1 (zagBasePoint i)) :=
        (zagHorizontal_pow_base e.1 i).symm
      _ = (zagHorizontal e.1 ^ i.val) (zagBasePoint i) := by rw [hebase]
      _ = (zagHorizontal f.1 ^ i.val) (zagBasePoint i) := by rw [hhorizontal]
      _ = (zagHorizontal f.1 ^ i.val) (f.1 (zagBasePoint i)) := by rw [hfbase]
      _ = f.1 i := zagHorizontal_pow_base f.1 i
  · intro s
    have htype : (finRotate n).cycleType = s.1.cycleType :=
      (zagCycleType_eq_finRotate_of_cycleCount_one hn s.1 s.2).symm
    have hconj := Equiv.Perm.isConj_of_cycleType_eq htype
    obtain ⟨e, he⟩ := isConj_iff.mp hconj
    let y : Fin n := e.symm z
    let e' : Equiv.Perm (Fin n) := e * (finRotate n) ^ y.val
    have he'base : e' (zagBasePoint z) = zagBasePoint z := by
      change e (((finRotate n) ^ y.val) z) = z
      have hpow : ((finRotate n) ^ y.val) z = y := by
        simpa only [z, zagBasePoint] using zagFinRotate_pow_base y
      rw [hpow]
      exact e.apply_symm_apply z
    refine ⟨⟨e', he'base⟩, Subtype.ext ?_⟩
    change zagHorizontal e' = s.1
    calc
      zagHorizontal e' = zagHorizontal e := by
        simp only [zagHorizontal, e', mul_inv_rev]
        group
      _ = s.1 := he

end MetaMathlibExt
