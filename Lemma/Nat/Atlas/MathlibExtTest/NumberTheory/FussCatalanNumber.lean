import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.FussCatalanNumber
open MetaMathlibExt


/--
[t10](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FussCatalanNumber.lean)
-/
@[path]
private lemma t10 : fussCatalanNumber 1 0 (by decide) = 1 :=
  rfl

/--
[t13](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FussCatalanNumber.lean)
-/
@[path]
private lemma t13 : fussCatalanNumber 1 3 (by decide) = 1 :=
  rfl

/--
[t20](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FussCatalanNumber.lean)
-/
@[path]
private lemma t20 : fussCatalanNumber 2 0 (by decide) = 1 :=
  rfl

/--
[t21](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FussCatalanNumber.lean)
-/
@[path]
private lemma t21 : fussCatalanNumber 2 1 (by decide) = 1 :=
  rfl

/--
[t22](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FussCatalanNumber.lean)
-/
@[path]
private lemma t22 : fussCatalanNumber 2 2 (by decide) = 2 :=
  rfl

/--
[t23](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FussCatalanNumber.lean)
-/
@[path]
private lemma t23 : fussCatalanNumber 2 3 (by decide) = 5 :=
  rfl

/--
[t32](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FussCatalanNumber.lean)
-/
@[path]
private lemma t32 : fussCatalanNumber 3 2 (by decide) = 3 :=
  rfl

/--
[fussCatalanNumber_proof_irrel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FussCatalanNumber.lean)
-/
@[path]
private lemma fussCatalanNumber_proof_irrel (h₁ h₂ : 1 ≤ 2) :
  fussCatalanNumber 2 3 h₁ = fussCatalanNumber 2 3 h₂ :=
  rfl


-- created on 2026-10-23
