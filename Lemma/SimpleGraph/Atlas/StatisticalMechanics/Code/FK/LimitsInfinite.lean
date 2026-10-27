import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.LimitsInfinite
open MeasureTheory Filter Topology StatMech StatMech.FK


/--
[weakLimit_extremality_of_common_subseq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitsInfinite.lean)
-/
@[path]
private lemma weakLimit_extremality_of_common_subseq_eq
  {d : ℕ}
  {p q : ℝ}
  {ν₀ ν₁ : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))}
  {ψ : ℕ → ℕ}
  {A : Set (ConfigSpace (Sym2 (Lattice.Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (h₀ : WeakConvergesTo (fun n => freeFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) ν₀)
  (h₁ : WeakConvergesTo (fun n => wiredFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) ν₁)
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A) :
-- imply
  (ν₀ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A ≤ (ν₁ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A := by
-- proof
  apply StatMech.FK.weakLimit_extremality_of_common_subseq d hp hp1 hq h₀ h₁ hAclopen hAinc

/--
[exists_common_subseq_weak_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitsInfinite.lean)
-/
@[path]
private lemma exists_common_subseq_weak_limits_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∃ (ψ : ℕ → ℕ) (ν₀ ν₁ : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))), StrictMono ψ ∧ WeakConvergesTo (fun n => freeFiniteMeasure d (ψ n) hp hp1 hq) ν₀ ∧ WeakConvergesTo (fun n => wiredFiniteMeasure d (ψ n) hp hp1 hq) ν₁ := by
-- proof
  apply StatMech.FK.exists_common_subseq_weak_limits d hp hp1 hq

/--
[exists_infiniteVolume_extremal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitsInfinite.lean)
-/
@[path]
private lemma exists_infiniteVolume_extremal_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  ∃ (ψ : ℕ → ℕ) (φ0 φ1 : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))), StrictMono ψ ∧ WeakConvergesTo (fun n => freeFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) φ0 ∧ WeakConvergesTo (fun n => wiredFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) φ1 ∧ ∀ A : Set (ConfigSpace (Sym2 (Lattice.Site d))), IsClopen A → IsIncreasing A → (φ0 : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A ≤ (φ1 : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A := by
-- proof
  apply StatMech.FK.exists_infiniteVolume_extremal d hp hp1 hq


-- created on 2026-10-23
