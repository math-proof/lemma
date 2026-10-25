import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.LieSimplicityBridge


/--
[LieSubmodule.mem_ofUEASubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/LieSimplicityBridge.lean)
-/
@[path]
lemma LieSubmodule.mem_ofUEASubmodule
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [Module (UniversalEnvelopingAlgebra R L) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
  {N : Submodule (UniversalEnvelopingAlgebra R L) M}
  {m : M}
-- given
  (hcompat : ∀ (x : L) (m : M), ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
-- imply
  m ∈ LieSubmodule.ofUEASubmodule hcompat N ↔ m ∈ N :=
-- proof
  Iff.rfl

/--
[isSimpleOrder_submodule_of_isIrreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/LieSimplicityBridge.lean)
-/
@[path]
lemma isSimpleOrder_submodule_of_isIrreducible
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [Module (UniversalEnvelopingAlgebra R L) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
  [hirr : LieModule.IsIrreducible R L M]
-- given
  (hcompat : ∀ (x : L) (m : M), ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
-- imply
  IsSimpleOrder (Submodule (UniversalEnvelopingAlgebra R L) M) := by
-- proof
  haveI hnt : Nontrivial M :=
    (LieSubmodule.nontrivial_iff R L M).mp hirr.toNontrivial
  haveI : Nontrivial (Submodule (UniversalEnvelopingAlgebra R L) M) :=
    (Submodule.nontrivial_iff (UniversalEnvelopingAlgebra R L)).mpr hnt
  apply IsSimpleOrder.of_forall_eq_top
  intro N hN
  have h := hirr.eq_bot_or_eq_top (LieSubmodule.ofUEASubmodule hcompat N)
  obtain hbot | htop := h
  ·
    exfalso
    apply hN
    ext m
    simp only [Submodule.mem_bot]
    constructor
    · intro hm
      have hmem : m ∈ LieSubmodule.ofUEASubmodule hcompat N :=
        (LieSubmodule.mem_ofUEASubmodule hcompat N m).mpr hm
      rw [hbot] at hmem
      exact (LieSubmodule.mem_bot m).mp hmem
    · intro hm
      rw [hm]; exact N.zero_mem
  ·
    ext m
    simp only [Submodule.mem_top, iff_true]
    have hmem : m ∈ LieSubmodule.ofUEASubmodule hcompat N := by
      rw [htop]; exact LieSubmodule.mem_top m
    exact (LieSubmodule.mem_ofUEASubmodule hcompat N m).mp hmem

/--
[LieModule.isSimpleModule_of_isIrreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/LieSimplicityBridge.lean)
-/
@[path]
lemma LieModule.isSimpleModule_of_isIrreducible
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [Module (UniversalEnvelopingAlgebra R L) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
  [hirr : LieModule.IsIrreducible R L M]
-- given
  (hcompat : ∀ (x : L) (m : M), ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
-- imply
  IsSimpleModule (UniversalEnvelopingAlgebra R L) M where __ :=
-- proof
  isSimpleOrder_submodule_of_isIrreducible hcompat


-- created on 2026-10-23
