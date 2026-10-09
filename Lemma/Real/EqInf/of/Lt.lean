import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {m M : ℝ}
-- given
  (h : m < M) :
-- imply
  sInf (Set.Ioo m M) = m := by
-- proof
  have hne : (Set.Ioo m M).Nonempty := Set.nonempty_Ioo.mpr h
  have h1 : m ≤ sInf (Set.Ioo m M) := le_csInf hne (fun x hx => hx.1.le)
  have h2 : sInf (Set.Ioo m M) ≤ m := by
    by_contra hcon
    have hmem : (m + sInf (Set.Ioo m M)) / 2 ∈ Set.Ioo m M := by
      constructor
      ·
        linarith
      ·
        obtain ⟨x, hx⟩ := hne
        have hsx : sInf (Set.Ioo m M) ≤ x := csInf_le ⟨m, fun y hy => hy.1.le⟩ hx
        have hx2 : x < M := hx.2
        linarith
    have hle : sInf (Set.Ioo m M) ≤ (m + sInf (Set.Ioo m M)) / 2 :=
      csInf_le ⟨m, fun y hy => hy.1.le⟩ hmem
    linarith
  exact le_antisymm h2 h1


-- created on 2019-08-27
