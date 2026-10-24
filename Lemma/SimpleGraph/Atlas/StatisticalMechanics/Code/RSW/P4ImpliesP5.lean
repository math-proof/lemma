import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.P4ImpliesP5
open Real Filter StatMech StatMech.RSW StatMech.RSW.P4ImpliesP5


/--
[rp4_expDecay_of_stretched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P4ImpliesP5.lean)
-/
@[path]
private lemma rp4_expDecay_of_stretched_eq
  {a : ℕ → ℝ}
-- given
  (hnn : ∀ n, 0 ≤ a n)
  (hle1 : ∀ n, a n ≤ 1)
  (hanti : Antitone a)
  (hsub : ∀ m n, a (m + n) ≤ a m * a n)
  (hstr : rp4_StretchedExpDecay a) :
-- imply
  rp4_ExpDecay a := by
-- proof
  apply StatMech.RSW.P4ImpliesP5.rp4_expDecay_of_stretched a hnn hle1 hanti hsub hstr

/--
[rp4_not_stretched_of_P4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P4ImpliesP5.lean)
-/
@[path]
private lemma rp4_not_stretched_of_P4_eq
  {a : ℕ → ℝ}
-- given
  (hnn : ∀ n, 0 ≤ a n)
  (hle1 : ∀ n, a n ≤ 1)
  (hanti : Antitone a)
  (hsub : ∀ m n, a (m + n) ≤ a m * a n)
  (hP4 : rp4_P4 a) :
-- imply
  ¬ rp4_StretchedExpDecay a := by
-- proof
  apply StatMech.RSW.P4ImpliesP5.rp4_not_stretched_of_P4 a hnn hle1 hanti hsub hP4

/--
[rp4_p4_implies_p5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P4ImpliesP5.lean)
-/
@[path]
private lemma rp4_p4_implies_p5_eq
  {a : ℕ → ℝ}
  {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))) → ℝ}
  {lam : ℕ → Set (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))) → ℝ}
-- given
  (hnn : ∀ n, 0 ≤ a n)
  (hle1 : ∀ n, a n ≤ 1)
  (hanti : Antitone a)
  (hsub : ∀ m n, a (m + n) ≤ a m * a n)
  (hP4 : rp4_P4 a)
  (hdich : rp5_P5b ν ∨ rp4_StretchedExpDecay a)
  (hchain : ∀ (α : ℝ) (n : ℕ), ν 2 n (annulusEvent n) ≤ lam n (boxCrossingEvent α n)) :
-- imply
  P5 lam := by
-- proof
  apply StatMech.RSW.P4ImpliesP5.rp4_p4_implies_p5 a hnn hle1 hanti hsub hP4 hdich hchain


-- created on 2026-10-23
