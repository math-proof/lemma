import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.RSW.P5Equivalences.Part2
open Set StatMech StatMech.RSW StatMech.RSW.Box


/--
[mem_annulusEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean)
-/
@[path]
private lemma mem_annulusEvent_eq
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ annulusEvent n ↔ AnnulusCircuit ω (fun _ => 0) n := by
-- proof
  apply StatMech.RSW.Box.mem_annulusEvent

/--
[rp5_p5a_p5b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean)
-/
@[path]
private lemma rp5_p5a_p5b_eq
  {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
  {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
-- given
  (hcmp : ∀ R n : ℕ, μ n (annulusEvent n) ≤ ν R n (annulusEvent n))
  (h : rp5_P5a μ) :
-- imply
  rp5_P5b ν := by
-- proof
  apply StatMech.RSW.Box.rp5_p5a_p5b hcmp h

/--
[rp5_p5_p5a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean)
-/
@[path]
private lemma rp5_p5_p5a_eq
  {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
-- given
  (hglue : ∀ n : ℕ, (μ n (boxCrossingEvent 10 n)) ^ 4 ≤ μ n (annulusEvent n))
  (h : P5 μ) :
-- imply
  rp5_P5a μ := by
-- proof
  apply StatMech.RSW.Box.rp5_p5_p5a hglue h

/--
[rp5_p5b_p5_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean)
-/
@[path]
private lemma rp5_p5b_p5_lower_eq
  {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
  {lam : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
-- given
  (hchain : ∀ (α : ℝ) (n : ℕ), ν 2 n (annulusEvent n) ≤ lam n (boxCrossingEvent α n))
  (h : rp5_P5b ν) :
-- imply
  P5 lam := by
-- proof
  apply StatMech.RSW.Box.rp5_p5b_p5_lower hchain h

/--
[rp5_p5b_p5_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean)
-/
@[path]
private lemma rp5_p5b_p5_upper_eq
  {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
  {compl : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
  {α : ℝ}
  {c : ℝ}
-- given
  (_hc : 0 < c)
  (hnorm : ∀ n : ℕ, μ n (boxCrossingEvent α n) + compl n (boxCrossingEvent α n) = 1)
  (hdual : ∀ n : ℕ, c ≤ compl n (boxCrossingEvent α n)) :
-- imply
  ∀ n : ℕ, μ n (boxCrossingEvent α n) ≤ 1 - c := by
-- proof
  apply StatMech.RSW.Box.rp5_p5b_p5_upper _hc hnorm hdual

/--
[rp5_p5_p5c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean)
-/
@[path]
private lemma rp5_p5_p5c_eq
  {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
-- given
  (hlower : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ (ξ : Ξ) (n : ℕ), c ≤ μ ξ n (boxCrossingEvent α n) ∧ μ ξ n (boxCrossingEvent α n) ≤ 1 - c) :
-- imply
  P5c μ := by
-- proof
  apply StatMech.RSW.Box.rp5_p5_p5c hlower

/--
[rp5_p5_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean)
-/
@[path]
private lemma rp5_p5_equiv_eq
  {ξ₀ : Ξ}
  {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
  {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
-- given
  (hcmp : ∀ R n : ℕ, μ ξ₀ n (annulusEvent n) ≤ ν R n (annulusEvent n))
  (hglue : ∀ n : ℕ, (μ ξ₀ n (boxCrossingEvent 10 n)) ^ 4 ≤ μ ξ₀ n (annulusEvent n))
  (hchain : ∀ (α : ℝ) (n : ℕ), ν 2 n (annulusEvent n) ≤ μ ξ₀ n (boxCrossingEvent α n))
  (htwo : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ (ξ : Ξ) (n : ℕ), c ≤ μ ξ n (boxCrossingEvent α n) ∧ μ ξ n (boxCrossingEvent α n) ≤ 1 - c) :
-- imply
  (P5 (μ ξ₀) ↔ rp5_P5a (μ ξ₀)) ∧ (rp5_P5a (μ ξ₀) → rp5_P5b ν) ∧ (rp5_P5b ν → P5 (μ ξ₀)) ∧ (P5 (μ ξ₀) ↔ P5c μ) := by
-- proof
  apply StatMech.RSW.Box.rp5_p5_equiv ξ₀ hcmp hglue hchain htwo


-- created on 2026-10-23
