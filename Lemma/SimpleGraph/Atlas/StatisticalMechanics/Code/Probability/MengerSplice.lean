import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.MengerSplice
open StatMech StatMech.Combinatorics


/--
[mgs_start_not_mem_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MengerSplice.lean)
-/
@[path]
private lemma mgs_start_not_mem_tail_eq
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath) :
-- imply
  u ∉ p.support.tail := by
-- proof
  apply StatMech.Combinatorics.mgs_start_not_mem_tail hp

/--
[mgs_append_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MengerSplice.lean)
-/
@[path]
private lemma mgs_append_isPath_eq
  {G : SimpleGraph V}
  {u v w : V}
  {p : G.Walk u v}
  {q : G.Walk v w}
-- given
  (hp : p.IsPath)
  (hq : q.IsPath)
  (hmeet : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
-- imply
  (p.append q).IsPath := by
-- proof
  apply StatMech.Combinatorics.mgs_append_isPath hp hq hmeet

/--
[mgs_spliced_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MengerSplice.lean)
-/
@[path]
private lemma mgs_spliced_isPath_eq
  {G : SimpleGraph V}
  {srcA tgtA wB : ι → V}
  {pA : (i : ι) → G.Walk (srcA i) (tgtA i)}
  {pB : (i : ι) → G.Walk (tgtA i) (wB i)}
  {S : Set V}
  {i : ι}
-- given
  (hApath : ∀ i, (pA i).IsPath)
  (hBpath : ∀ i, (pB i).IsPath)
  (hAmeetB : ∀ i i' x, x ∈ (pA i).support → x ∈ (pB i').support → x ∈ S)
  (hAcapS : ∀ i x, x ∈ (pA i).support → x ∈ S → x = tgtA i) :
-- imply
  (mgs_spliced pA pB i).IsPath := by
-- proof
  apply StatMech.Combinatorics.mgs_spliced_isPath pA pB hApath hBpath hAmeetB hAcapS i

/--
[mgs_spliced_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MengerSplice.lean)
-/
@[path]
private lemma mgs_spliced_disjoint_eq
  {G : SimpleGraph V}
  {srcA tgtA wB : ι → V}
  {pA : (i : ι) → G.Walk (srcA i) (tgtA i)}
  {pB : (i : ι) → G.Walk (tgtA i) (wB i)}
  {S : Set V}
  {i i' : ι}
  {x : V}
-- given
  (hAinj : Function.Injective tgtA)
  (hAA : ∀ i i', i ≠ i' → ∀ x, x ∈ (pA i).support → x ∈ (pA i').support → False)
  (hBB : ∀ i i', i ≠ i' → ∀ x, x ∈ (pB i).support → x ∈ (pB i').support → False)
  (hAmeetB : ∀ i i' x, x ∈ (pA i).support → x ∈ (pB i').support → x ∈ S)
  (hAcapS : ∀ i x, x ∈ (pA i).support → x ∈ S → x = tgtA i)
  (hBcapS : ∀ i x, x ∈ (pB i).support → x ∈ S → x = tgtA i)
  (hii : i ≠ i')
  (hxi : x ∈ (mgs_spliced pA pB i).support)
  (hxi' : x ∈ (mgs_spliced pA pB i').support) :
-- imply
  False := by
-- proof
  apply StatMech.Combinatorics.mgs_spliced_disjoint pA pB hAinj hAA hBB hAmeetB hAcapS hBcapS hii hxi hxi'


-- created on 2026-10-23
