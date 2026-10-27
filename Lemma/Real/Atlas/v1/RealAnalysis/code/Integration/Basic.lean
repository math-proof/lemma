import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.RealAnalysis.code.Integration.Basic.Part2
open Integration
open Set Filter Topology


namespace Integration

/--
[Partition.n_pos_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Basic.lean)
-/
@[path]
lemma Partition.n_pos_of_lt
  {a b : ℝ}
  {P : Partition a b}
-- given
  (hab : a < b) :
-- imply
  0 < P.n := by
-- proof
  by_contra h
  have hn : P.n = 0 := by omega
  have hlast : Fin.last P.n = (0 : Fin (P.n + 1)) := by ext; simp [hn]
  have := P.last; rw [hlast] at this
  linarith [P.first]

end Integration

namespace Integration

/--
[Partition.mesh_pos_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Basic.lean)
-/
@[path]
lemma Partition.mesh_pos_of_lt
  {a b : ℝ}
  {P : Partition a b}
-- given
  (hab : a < b) :
-- imply
  0 < P.mesh := by
-- proof
  have hn : P.n ≠ 0 := (P.n_pos_of_lt hab).ne'
  have i₀ : Fin P.n := ⟨0, Nat.pos_of_ne_zero hn⟩
  unfold Partition.mesh
  rw [dif_neg hn]
  have hlt : P.points i₀.castSucc < P.points i₀.succ :=
    P.ordered Fin.castSucc_lt_succ
  calc (0 : ℝ) < P.points i₀.succ - P.points i₀.castSucc := sub_pos.mpr hlt
    _ ≤ Finset.sup' Finset.univ _
      (fun (i : Fin P.n) => P.points i.succ - P.points i.castSucc) :=
      Finset.le_sup' (fun (i : Fin P.n) => P.points i.succ - P.points i.castSucc)
        (Finset.mem_univ i₀)

end Integration

namespace Integration

/--
[riemannSum_eq_zero_of_n_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Basic.lean)
-/
@[path]
lemma riemannSum_eq_zero_of_n_eq_zero
  {a b : ℝ}
  {f : ℝ → ℝ}
  {T : TaggedPartition a b}
-- given
  (h : T.n = 0) :
-- imply
  riemannSum f T = 0 := by
-- proof
  unfold riemannSum
  have : IsEmpty (Fin T.n) := by rw [h]; infer_instance
  exact Fintype.sum_empty _

end Integration


-- created on 2026-10-23
