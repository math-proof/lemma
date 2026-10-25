import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWLemma5
open StatMech StatMech.Onsager


/--
[kw_rev_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLemma5.lean)
-/
@[path]
private lemma kw_rev_factor_eq
  {L : ℕ}
  {x ω : ℂ}
  {a b : ons_Dart L} :
-- imply
  ons_KWmat L x ω (ons_dartRev L a) (ons_dartRev L b) = if ons_dirStep L a.2 a.1 = b.1 then x * (ons_turnW ω a.2 b.2)⁻¹ else 0 := by
-- proof
  apply StatMech.Onsager.kw_rev_factor x ω a b

/--
[ons_turnW_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLemma5.lean)
-/
@[path]
private lemma ons_turnW_swap_eq
  {ω : ℂ}
  {μ ν : Fin 4} :
-- imply
  ons_turnW ω ν μ = (ons_turnW ω μ ν)⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_turnW_swap ω μ ν

/--
[ons_interior_turn_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLemma5.lean)
-/
@[path]
private lemma ons_interior_turn_sq_eq
  {ω : ℂ}
  {N : ℕ}
  {d : Fin (N + 1) → Fin 4}
-- given
  (hω : ω ≠ 0)
  (hI : ω ^ 2 = Complex.I)
  (hnu : ∀ k : Fin N, d k.succ ≠ d k.castSucc + 2)
  (hend : d (Fin.last N) = d 0 + 2) :
-- imply
  (∏ j : Fin N, ons_turnW ω (d j.succ) (d j.castSucc)) ^ 2 = -1 := by
-- proof
  apply StatMech.Onsager.ons_interior_turn_sq ω hω hI N d hnu hend

/--
[ons_KW_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLemma5.lean)
-/
@[path]
private lemma ons_KW_surgery_sign_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {x ω : ℂ}
  {e : ons_Dart L}
  {v : Fin n → ons_Dart L}
-- given
  (hω : ω ^ 2 = Complex.I)
  (hv : v ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
-- imply
  ons_loopWeight (ons_KWmat L x ω) (ons_surgery e (ons_dartRev L) v) = -ons_loopWeight (ons_KWmat L x ω) v := by
-- proof
  apply StatMech.Onsager.ons_KW_surgery_sign x ω hω e v hv

/--
[ons_KW_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLemma5.lean)
-/
@[path]
private lemma ons_KW_lemma5_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {x ω : ℂ}
  {e : ons_Dart L}
-- given
  (hω : ω ^ 2 = Complex.I) :
-- imply
  ∑ v ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e), ons_loopWeight (ons_KWmat L x ω) v = 0 := by
-- proof
  apply StatMech.Onsager.ons_KW_lemma5 x ω hω e


-- created on 2026-10-23
