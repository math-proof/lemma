import stdlib.List.Vector
import Lemma.Algebra.ValGetUnflatten.eq.ValSubStr
import Lemma.Logic.All_And.of.All.All
import Lemma.Logic.All.of.All.All_Imp
import Lemma.Algebra.Eq.of.EqValS
import Lemma.Algebra.Eq_MapRange_FunGet
import Lemma.Algebra.Eq_FlattenUnflatten
open Algebra Logic


@[main]
private lemma main
  [Inhabited α]
  {v : List.Vector α (m * n)}
  {u : Fin m → List.Vector α n}
-- given
  (h : ∀ i : Fin m, (v.substr (i * n) n).val = (u i).val) :
-- imply
  v = ((List.Vector.range m).map fun i => u i).flatten := by
-- proof
  have h_All := ValGetUnflatten.eq.ValSubStr v
  have h_All_And := All_And.of.All.All h_All h
  have h_All_Imp : ∀ (i : Fin m), v.unflatten[i].val = (v.substr (i * n) n).val ∧ (v.substr (i * n) n).val = (u i).val → v.unflatten[i].val = (u i).val := by
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
