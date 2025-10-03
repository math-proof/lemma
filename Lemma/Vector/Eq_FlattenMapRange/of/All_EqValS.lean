import sympy.vector.vector
import Lemma.Vector.ValGetUnflatten.eq.ValArraySlice
import Lemma.Logic.All_And.of.All.All
import Lemma.Logic.All.of.All.All_Imp
import Lemma.Vector.Eq.of.EqValS
import Lemma.Vector.Eq_MapRange_FunGet
import Lemma.Vector.EqFlattenUnflatten
open Logic Vector


@[main]
private lemma main
  {v : List.Vector α (m * n)}
  {u : Fin m → List.Vector α n}
-- given
  (h : ∀ i : Fin m, (v.array_slice (i * n) n).val = (u i).val) :
-- imply
  v = ((List.Vector.range m).map fun i => u i).flatten := by
-- proof
  have h_All := ValGetUnflatten.eq.ValArraySlice v
  have h_All_And := All_And.of.All.All h_All h
  have h_All_Imp : ∀ (i : Fin m), v.unflatten[i].val = (v.array_slice (i * n) n).val ∧ (v.array_slice (i * n) n).val = (u i).val → v.unflatten[i].val = (u i).val := by
    intro i ⟨h₀, h₁⟩
    apply h₀.trans h₁
  have h_All := All.of.All.All_Imp h_All_Imp h_All_And
  have h_All : ∀ i : Fin m, u i = v.unflatten[i] := by
    intro i
    have := h_All i
    apply Eq.symm
    apply Eq.of.EqValS this
  simp only [h_All]
  rw [← Eq_MapRange_FunGet v.unflatten]
  exact Eq_FlattenUnflatten v


-- created on 2025-05-07
-- updated on 2025-05-10
