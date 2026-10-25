import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnBaseFlag.Part3
open GLnBuilding


/--
[stdFlagSubspace_generators_linIndep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagSubspace_generators_linIndep_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {i : Fin (n - 1)} :
-- imply
  LinearIndependent k (fun (j : Fin (i.val + 1)) => (Pi.basisFun k (Fin n)) (⟨j.val, by omega⟩ : Fin n)) := by
-- proof
  apply GLnBuilding.stdFlagSubspace_generators_linIndep k n i

/--
[stdFlagSubspace_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagSubspace_finrank_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {i : Fin (n - 1)} :
-- imply
  Module.finrank k ↥(stdFlagSubspace k n i) = i.val + 1 := by
-- proof
  apply GLnBuilding.stdFlagSubspace_finrank k n i

/--
[stdFlagSubspace_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagSubspace_mono_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {i j : Fin (n - 1)}
-- given
  (h : i ≤ j) :
-- imply
  stdFlagSubspace k n i ≤ stdFlagSubspace k n j := by
-- proof
  apply GLnBuilding.stdFlagSubspace_mono k n h

/--
[stdFlagSubspace_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagSubspace_strictMono_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {i j : Fin (n - 1)}
-- given
  (h : i < j) :
-- imply
  stdFlagSubspace k n i < stdFlagSubspace k n j := by
-- proof
  apply GLnBuilding.stdFlagSubspace_strictMono k n h

/--
[stdFlagSubspace_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagSubspace_ne_bot_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {i : Fin (n - 1)} :
-- imply
  stdFlagSubspace k n i ≠ ⊥ := by
-- proof
  apply GLnBuilding.stdFlagSubspace_ne_bot k n i

/--
[stdFlagSubspace_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagSubspace_ne_top_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {i : Fin (n - 1)} :
-- imply
  stdFlagSubspace k n i ≠ ⊤ := by
-- proof
  apply GLnBuilding.stdFlagSubspace_ne_top k n i

/--
[stdFlagChain_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagChain_length_eq
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  (stdFlagChain k n).length = n - 1 := by
-- proof
  apply GLnBuilding.stdFlagChain_length k n

/--
[stdFlagChain_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagChain_isChain_eq
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  (stdFlagChain k n).IsChain (· < ·) := by
-- proof
  apply GLnBuilding.stdFlagChain_isChain k n

/--
[stdFlagChain_proper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean)
-/
@[path]
private lemma stdFlagChain_proper_eq
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  ∀ V ∈ stdFlagChain k n, V ≠ ⊥ ∧ V ≠ ⊤ := by
-- proof
  apply GLnBuilding.stdFlagChain_proper k n


-- created on 2026-10-23
