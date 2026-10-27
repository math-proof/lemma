import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.UniqueGames.Part8
open UniqueGames
open Finset


namespace UniqueGames

/--
[fractionSatisfied_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean)
-/
@[path]
lemma fractionSatisfied_le_one
  [DecidableEq X]
  [Fintype X]
  {k : ℕ}
  [DecidableEq V]
  [DecidableEq W]
  {k : ℕ}
  {game : UniqueGame V W k}
  {labeling : Labeling V W k} :
-- imply
  fractionSatisfied game labeling ≤ 1 := by
-- proof
  unfold fractionSatisfied numSatisfiedEdges numEdges
  by_cases h : (game.edges.card : ℝ) = 0
  · simp [h]
  · rw [div_le_one (by positivity : (0 : ℝ) < (game.edges.card : ℝ))]
    exact_mod_cast Finset.card_filter_le _ _

end UniqueGames

namespace UniqueGames

/--
[bddAbove_fractionSatisfied](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean)
-/
@[path]
lemma bddAbove_fractionSatisfied
  [DecidableEq X]
  [Fintype X]
  {k : ℕ}
  [DecidableEq V]
  [DecidableEq W]
  {k : ℕ}
  {game : UniqueGame V W k} :
-- imply
  BddAbove (Set.range (fun labeling : Labeling V W k => fractionSatisfied game labeling)) :=
-- proof
  ⟨1, fun _ ⟨lab, hlab⟩ => hlab ▸ fractionSatisfied_le_one game lab⟩

end UniqueGames

namespace UniqueGames

/--
[fractionSatisfied_le_value](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean)
-/
@[path]
lemma fractionSatisfied_le_value
  [DecidableEq X]
  [Fintype X]
  {k : ℕ}
  [DecidableEq V]
  [DecidableEq W]
  {k : ℕ}
  {game : UniqueGame V W k}
  {labeling : Labeling V W k} :
-- imply
  fractionSatisfied game labeling ≤ value game :=
-- proof
  le_ciSup (bddAbove_fractionSatisfied game) labeling

end UniqueGames

namespace UniqueGames

/--
[fractionSatisfied_le_of_value_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean)
-/
@[path]
lemma fractionSatisfied_le_of_value_le
  [DecidableEq X]
  [Fintype X]
  {k : ℕ}
  [DecidableEq V]
  [DecidableEq W]
  {k : ℕ}
  {game : UniqueGame V W k}
  {δ : ℝ}
  {labeling : Labeling V W k}
-- given
  (hval : value game ≤ δ) :
-- imply
  fractionSatisfied game labeling ≤ δ :=
-- proof
  le_trans (fractionSatisfied_le_value game labeling) hval
end UniqueGames
namespace MaxCut
open Finset


/--
[longCode_MIS_stabBound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean)
-/
@[path]
lemma longCode_MIS_stabBound
  {ρ : ℝ}
  {ε' : ℝ}
-- given
  (hρ_pos : 0 < ρ)
  (hρ_lt : ρ < 1)
  (hε' : ε' > 0) :
-- imply
  ∃ δ_MIS > 0, ∀ (k : ℕ) (δ : ℝ), 0 < δ → δ ≤ δ_MIS → δ < 1 → maxBalancedNoiseStab ρ δ k ≤ 1 - (2 / Real.pi) * Real.arccos ρ + ε' := by
-- proof
  obtain ⟨δ_MIS, hδ_MIS_pos, hMIS⟩ := mis_combinatorial_bound ρ hρ_pos hρ_lt ε' hε'
  refine ⟨δ_MIS, hδ_MIS_pos, fun k δ hδ_pos hδ_le hδ_lt => ?_⟩
  unfold maxBalancedNoiseStab
  set S := {s : ℝ | ∃ (f : (Fin k → Bool) → ℝ),
    (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ i : Fin k, (1 / (2 : ℝ) ^ k) *
      ∑ x : Fin k → Bool, (f x - f (Function.update x i (!x i))) ^ 2 / 4 ≤ δ) ∧
    ((1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x = 0) ∧
    s = (1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x *
      ((1 / (2 : ℝ) ^ k) * ∑ y : Fin k → Bool,
        (∏ i : Fin k, if x i = y i then 1 else ρ) * f y)}
  by_cases hne : S.Nonempty
  ·
    apply csSup_le hne
    intro s hs
    obtain ⟨f, hbnd, hinf, hbal, hs_eq⟩ := hs
    rw [hs_eq]
    have hinf_MIS : ∀ i : Fin k, (1 / (2 : ℝ) ^ k) *
      ∑ x : Fin k → Bool, (f x - f (Function.update x i (!x i))) ^ 2 / 4 ≤ δ_MIS := fun i =>
      le_trans (hinf i) hδ_le
    exact hMIS k f hbnd hinf_MIS hbal
  ·
    have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Real.sSup_empty]
    have harccos_lt : Real.arccos ρ < Real.pi / 2 :=
      Real.arccos_lt_pi_div_two.mpr hρ_pos
    have h_frac : 2 / Real.pi * Real.arccos ρ < 1 := by
      have h1 : 2 / Real.pi * Real.arccos ρ < 2 / Real.pi * (Real.pi / 2) :=
        mul_lt_mul_of_pos_left harccos_lt (by positivity)
      linarith [show 2 / Real.pi * (Real.pi / 2) = 1 from by field_simp]
    linarith


-- created on 2026-10-23
