/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Def.Combinatorics.SimpleGraph.EdgeGraceful
import Lemma.SimpleGraph.EdgeGraceful
import Def.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful.Part3


namespace EdgeGracefulTest

/-- The 3-vertex path is graceful with residues `1, 0, 2`. -/
example : (SimpleGraph.pathGraph 3).IsEdgeGraceful := by
  classical
  have hne : Fintype.card (Fin 3) ≠ 0 := by simp
  have hc3 : Fintype.card (Fin 3) = 3 := by simp
  have h0 : (pathLabel.symm 0).val = Sym2.mk (0 : Fin 3) 1 := rfl
  have h1 : (pathLabel.symm 1).val = Sym2.mk (1 : Fin 3) 2 := rfl
  have m00 : (0 : Fin 3) ∈ (pathLabel.symm 0).val := by
    rw [h0]; exact Sym2.mem_mk_left _ _
  have m01 : (0 : Fin 3) ∉ (pathLabel.symm 1).val := by
    rw [h1]; simp only [Sym2.mem_iff]; decide
  have m10 : (1 : Fin 3) ∈ (pathLabel.symm 0).val := by
    rw [h0]; exact Sym2.mem_mk_right _ _
  have m11 : (1 : Fin 3) ∈ (pathLabel.symm 1).val := by
    rw [h1]; exact Sym2.mem_mk_left _ _
  have m20 : (2 : Fin 3) ∉ (pathLabel.symm 0).val := by
    rw [h0]; simp only [Sym2.mem_iff]; decide
  have m21 : (2 : Fin 3) ∈ (pathLabel.symm 1).val := by
    rw [h1]; exact Sym2.mem_mk_right _ _
  have s0 : (SimpleGraph.pathGraph 3).incidentSum 2 pathLabel 0 = 1 := by
    unfold SimpleGraph.incidentSum
    simp [Fin.sum_univ_two, m00, m01]
  have s1 : (SimpleGraph.pathGraph 3).incidentSum 2 pathLabel 1 = 3 := by
    unfold SimpleGraph.incidentSum
    simp [Fin.sum_univ_two, m10, m11]
  have s2 : (SimpleGraph.pathGraph 3).incidentSum 2 pathLabel 2 = 2 := by
    unfold SimpleGraph.incidentSum
    simp [Fin.sum_univ_two, m20, m21]
  have r0 : ((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel 0).val = 1 := by
    rw [SimpleGraph.inducedResidue_val _ 2 pathLabel 0 hne, s0, hc3]
  have r1 : ((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel 1).val = 0 := by
    rw [SimpleGraph.inducedResidue_val _ 2 pathLabel 1 hne, s1, hc3]
  have r2 : ((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel 2).val = 2 := by
    rw [SimpleGraph.inducedResidue_val _ 2 pathLabel 2 hne, s2, hc3]
  refine ⟨2, pathLabel, ?_⟩
  have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have hfun : ((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel) =
      ⇑((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)) := by
    funext x
    fin_cases x
    · apply Fin.ext
      change ((((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel) 0).val) =
        (((((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)) 0)).val)
      rw [r0]
      simp [Equiv.trans_apply, e0]
    · apply Fin.ext
      change ((((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel) 1).val) =
        (((((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)) 1)).val)
      rw [r1]
      simp [Equiv.trans_apply, e1]
    · apply Fin.ext
      change ((((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel) 2).val) =
        (((((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)) 2)).val)
      rw [r2]
      simp [Equiv.trans_apply, e2]
  rw [hfun]
  exact ((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)).bijective

end EdgeGracefulTest
