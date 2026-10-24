import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc5_minimalwitnessencoded
open Finset StatMech StatMech.Walls


/--
[occursMinimalWitness_iff_supportEncoded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma occursMinimalWitness_iff_supportEncoded_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E} :
-- imply
  OccursMinimalWitness A B ω s K L ↔ SupportEncodedMinimalWitness A B ω s K L := by
-- proof
  apply StatMech.Walls.occursMinimalWitness_iff_supportEncoded

/--
[occursOn_supportCfg_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma occursOn_supportCfg_of_support_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s : Finset E}
  {K : Finset E}
-- given
  (hs : s = cfgSupport ω) :
-- imply
  OccursOn A (↑K) (supportCfg s) ↔ OccursOn A (↑K) ω := by
-- proof
  apply StatMech.Walls.occursOn_supportCfg_of_support hs K

/--
[occursOn_iff_supportSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma occursOn_iff_supportSlice_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s : Finset E}
  {K : Finset E}
  {ω' : ConfigSpace E}
-- given
  (hs : s = cfgSupport ω) :
-- imply
  ω' ∈ cylinder K (supportCfg s) ↔ cfgSupport ω' ∩ K = s ∩ K := by
-- proof
  apply StatMech.Walls.occursOn_iff_supportSlice hs K ω'

/--
[occursOn_of_occursEncoding_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma occursOn_of_occursEncoding_decode_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : OccursMinimalWitness A B ω s K L) :
-- imply
  OccursOn A (↑K) (supportCfg s) ∧ OccursOn B (↑L) (supportCfg s) := by
-- proof
  apply StatMech.Walls.occursOn_of_occursEncoding_decode h

/--
[exists_occursMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma exists_occursMinimalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  ∃ s K L : Finset E, OccursMinimalWitness A B ω s K L := by
-- proof
  apply StatMech.Walls.exists_occursMinimalWitness hω

/--
[mem_of_occursMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma mem_of_occursMinimalWitness_eq
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
  apply StatMech.Walls.mem_of_occursMinimalWitness h

/--
[mem_disjointOccurrence_iff_occursMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma mem_disjointOccurrence_iff_occursMinimalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ disjointOccurrence A B ↔ ∃ s K L : Finset E, OccursMinimalWitness A B ω s K L := by
-- proof
  apply StatMech.Walls.mem_disjointOccurrence_iff_occursMinimalWitness

/--
[occursOn_of_occursMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma occursOn_of_occursMinimalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : OccursMinimalWitness A B ω s K L) :
-- imply
  OccursOn A (↑K) ω ∧ OccursOn B (↑L) ω ∧ Disjoint K L := by
-- proof
  apply StatMech.Walls.occursOn_of_occursMinimalWitness h

/--
[not_occursOn_of_lt_minimalA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma not_occursOn_of_lt_minimalA_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L S : Finset E}
-- given
  (h : OccursMinimalWitness A B ω s K L)
  (hlt : S ⊂ K) :
-- imply
  ¬ OccursOn A (↑S) ω := by
-- proof
  apply StatMech.Walls.not_occursOn_of_lt_minimalA h hlt

/--
[not_occursOn_of_lt_minimalB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma not_occursOn_of_lt_minimalB_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L S : Finset E}
-- given
  (h : OccursMinimalWitness A B ω s K L)
  (hlt : S ⊂ L) :
-- imply
  ¬ OccursOn B (↑S) ω := by
-- proof
  apply StatMech.Walls.not_occursOn_of_lt_minimalB h hlt

/--
[supportCfg_of_occursMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma supportCfg_of_occursMinimalWitness_eq
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
  apply StatMech.Walls.supportCfg_of_occursMinimalWitness h

/--
[support_eq_cfgEquivFinset_of_occursMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma support_eq_cfgEquivFinset_of_occursMinimalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : OccursMinimalWitness A B ω s K L) :
-- imply
  s = cfgEquivFinset ω := by
-- proof
  apply StatMech.Walls.support_eq_cfgEquivFinset_of_occursMinimalWitness h

/--
[exists_occursMinimalWitness_of_disjoint_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_minimalwitnessencoded.lean)
-/
@[path]
private lemma exists_occursMinimalWitness_of_disjoint_witness_eq
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
  ∃ s K' L' : Finset E, OccursMinimalWitness A B ω s K' L' := by
-- proof
  apply StatMech.Walls.exists_occursMinimalWitness_of_disjoint_witness hKL hA hB


-- created on 2026-10-23
