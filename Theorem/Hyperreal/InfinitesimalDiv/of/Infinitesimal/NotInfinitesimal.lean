module

public import Theorem.Hyperreal.NotInfinitesimal.is.Any_GeAbs
public import Theorem.Nat.Gt.of.Ge.Gt
public import Theorem.Nat.LeMulS.of.Le.Gt_0
public import Theorem.Rat.AbsDiv.eq.DivAbsS
public import Theorem.Rat.LtDiv.is.Lt_Mul.of.Gt_0

public section

open Hyperreal Nat Rat


/--
the hypotheses are arranged in the constructor order of division a / b
-/
@[mt]
public theorem Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
  {a b : ℝ*}
-- given
  (h_a : a → 0)
  (h_b : ¬b → 0) :
-- imply
  (a / b) → 0 := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  intro ⟨δ, hδ⟩
  simp [AbsDiv.eq.DivAbsS]
  let ⟨⟨B, h_B⟩, h_B_le⟩ := Any_GeAbs.of.NotInfinitesimal h_b
  apply LtDiv.of.Lt_Mul.Gt_0
  ·
    apply Gt.of.Ge.Gt h_B_le
    simpa
  ·
    have h_a := All_LtAbs.of.Infinitesimal h_a
    calc _ < _ := h_a ⟨B * δ, by nlinarith⟩
      _ ≤ _ := LeMulS.of.Le.Gt_0 h_B_le (by simpa)


-- created on 2025-12-09
