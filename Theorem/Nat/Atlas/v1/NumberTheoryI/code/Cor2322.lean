module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.NumberTheoryI.code.Cor2322

public section

open CategoryTheory Limits in


/--
[mapRange_linearMap_add_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2322.lean)
-/
@[path]
public theorem mapRange_linearMap_add_apply_eq
  {k : Type u}
  [CommRing k]
  {α M N : Type u}
  [AddCommGroup M]
  [Module k M]
  [AddCommGroup N]
  [Module k N]
  {f g : M →ₗ[k] N}
  {x : α →₀ M} :
-- imply
  Finsupp.mapRange.linearMap (f + g) x = Finsupp.mapRange.linearMap f x + Finsupp.mapRange.linearMap g x := by
-- proof
  apply mapRange_linearMap_add_apply f g x


-- created on 2026-10-23
