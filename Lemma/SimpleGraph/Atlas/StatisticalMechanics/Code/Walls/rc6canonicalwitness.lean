import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc6canonicalwitness
open Finset StatMech StatMech.Walls


/--
[occursMinimalWitness_support_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma occursMinimalWitness_support_unique_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s s' K K' L L' : Finset E}
-- given
  (h : OccursMinimalWitness A B ω s K L)
  (h' : OccursMinimalWitness A B ω s' K' L') :
-- imply
  s = s' := by
-- proof
  apply StatMech.Walls.occursMinimalWitness_support_unique h h'

/--
[occursMinimalWitness_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma occursMinimalWitness_decode_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : OccursMinimalWitness A B ω s K L) :
-- imply
  supportCfg s = ω := by
-- proof
  apply StatMech.Walls.occursMinimalWitness_decode h

/--
[canonicalWitness_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_spec_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  OccursMinimalWitness A B ω (canonicalWitness A B ω).1 (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 := by
-- proof
  apply StatMech.Walls.canonicalWitness_spec hω

/--
[canonicalWitness_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_support_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  (canonicalWitness A B ω).1 = cfgSupport ω := by
-- proof
  apply StatMech.Walls.canonicalWitness_support hω

/--
[canonicalWitness_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_disjoint_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  Disjoint (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 := by
-- proof
  apply StatMech.Walls.canonicalWitness_disjoint hω

/--
[canonicalWitness_minimalA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_minimalA_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  Minimal (fun S : Finset E => OccursOn A (↑S) ω) (canonicalWitness A B ω).2.1 := by
-- proof
  apply StatMech.Walls.canonicalWitness_minimalA hω

/--
[canonicalWitness_minimalB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_minimalB_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  Minimal (fun S : Finset E => OccursOn B (↑S) ω) (canonicalWitness A B ω).2.2 := by
-- proof
  apply StatMech.Walls.canonicalWitness_minimalB hω

/--
[canonicalWitness_occursOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_occursOn_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  OccursOn A (↑(canonicalWitness A B ω).2.1) ω ∧ OccursOn B (↑(canonicalWitness A B ω).2.2) ω ∧ Disjoint (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 := by
-- proof
  apply StatMech.Walls.canonicalWitness_occursOn hω

/--
[canonicalWitness_not_occursOn_ssubsetA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_not_occursOn_ssubsetA_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {S : Finset E}
-- given
  (hω : ω ∈ disjointOccurrence A B)
  (hlt : S ⊂ (canonicalWitness A B ω).2.1) :
-- imply
  ¬ OccursOn A (↑S) ω := by
-- proof
  apply StatMech.Walls.canonicalWitness_not_occursOn_ssubsetA hω hlt

/--
[canonicalWitness_not_occursOn_ssubsetB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_not_occursOn_ssubsetB_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {S : Finset E}
-- given
  (hω : ω ∈ disjointOccurrence A B)
  (hlt : S ⊂ (canonicalWitness A B ω).2.2) :
-- imply
  ¬ OccursOn B (↑S) ω := by
-- proof
  apply StatMech.Walls.canonicalWitness_not_occursOn_ssubsetB hω hlt

/--
[canonicalWitness_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_decode_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  supportCfg (canonicalWitness A B ω).1 = ω := by
-- proof
  apply StatMech.Walls.canonicalWitness_decode hω

/--
[canonicalWitness_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_mem_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : OccursMinimalWitness A B ω s K L) :
-- imply
  ω ∈ disjointOccurrence A B := by
-- proof
  apply StatMech.Walls.canonicalWitness_mem h

/--
[canonicalWitness_decode_occursOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_decode_occursOn_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  OccursOn A (↑(canonicalWitness A B ω).2.1) (supportCfg (canonicalWitness A B ω).1) ∧ OccursOn B (↑(canonicalWitness A B ω).2.2) (supportCfg (canonicalWitness A B ω).1) := by
-- proof
  apply StatMech.Walls.canonicalWitness_decode_occursOn hω

/--
[mem_disjointOccurrence_iff_canonicalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma mem_disjointOccurrence_iff_canonicalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ disjointOccurrence A B ↔ OccursMinimalWitness A B ω (canonicalWitness A B ω).1 (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 := by
-- proof
  apply StatMech.Walls.mem_disjointOccurrence_iff_canonicalWitness

/--
[mem_disjointOccurrence_iff_exists_via_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma mem_disjointOccurrence_iff_exists_via_canonical_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ disjointOccurrence A B ↔ ∃ s K L : Finset E, OccursMinimalWitness A B ω s K L := by
-- proof
  apply StatMech.Walls.mem_disjointOccurrence_iff_exists_via_canonical

/--
[canonicalWitness_spec_of_disjoint_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean)
-/
@[path]
private lemma canonicalWitness_spec_of_disjoint_witness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {K L : Set E}
-- given
  (hKL : Disjoint K L)
  (hA : OccursOn A K ω)
  (hB : OccursOn B L ω) :
-- imply
  OccursMinimalWitness A B ω (canonicalWitness A B ω).1 (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 := by
-- proof
  apply StatMech.Walls.canonicalWitness_spec_of_disjoint_witness hKL hA hB


-- created on 2026-10-23
