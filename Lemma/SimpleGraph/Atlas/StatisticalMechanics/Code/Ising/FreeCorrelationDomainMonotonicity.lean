import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.FreeCorrelationDomainMonotonicity
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[couplingIn_nested](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeCorrelationDomainMonotonicity.lean)
-/
@[path]
private lemma couplingIn_nested_eq
  [Fintype V]
  [DecidableEq V]
  {J : Sym2 V -> Real}
  {S T : Finset V}
-- given
  (hST : S ⊆ T) :
-- imply
  couplingIn (couplingIn J T) S = couplingIn J S := by
-- proof
  apply StatMech.Sharpness.couplingIn_nested hST

/--
[expectationJ_couplingIn_mono_domain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeCorrelationDomainMonotonicity.lean)
-/
@[path]
private lemma expectationJ_couplingIn_mono_domain_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {S T : Finset V}
  {A : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hST : S ⊆ T) :
-- imply
  expectationJ G beta (couplingIn J S) A <= expectationJ G beta (couplingIn J T) A := by
-- proof
  apply StatMech.Sharpness.expectationJ_couplingIn_mono_domain beta J hbeta hJ hST A

/--
[freeCorr_mono_domain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeCorrelationDomainMonotonicity.lean)
-/
@[path]
private lemma freeCorr_mono_domain_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
  {beta : Real}
  {S T : Finset (Site d)}
  {a b : Site d}
-- given
  (hbeta : 0 <= beta)
  (hST : S ⊆ T)
  (haS : a ∈ S)
  (hbS : b ∈ S) :
-- imply
  freeCorr d beta S ⟨a, haS⟩ ⟨b, hbS⟩ <= freeCorr d beta T ⟨a, hST haS⟩ ⟨b, hST hbS⟩ := by
-- proof
  apply StatMech.Sharpness.freeCorr_mono_domain hbeta hST haS hbS


-- created on 2026-10-23
