import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.LieGroups.code.DModules
open DModules


/--
[liftKaehlerDifferential_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModules.lean)
-/
@[path]
private lemma liftKaehlerDifferential_smul_eq
  {k : Type u}
  [CommRing k]
  {A : Type v}
  [CommRing A]
  [Algebra k A]
  {M : Type w}
  [AddCommGroup M]
  [Module k M]
  [Module A M]
  [IsScalarTower k A M]
  {f : A}
  {v : Derivation k A A} :
-- imply
  (f • v).liftKaehlerDifferential = f • v.liftKaehlerDifferential := by
-- proof
  apply DModules.liftKaehlerDifferential_smul f v


-- created on 2026-10-23
