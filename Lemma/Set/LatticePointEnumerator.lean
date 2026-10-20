import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.LatticePointEnumerator
open scoped Pointwise
open LatticePointEnumerator


/--
[mem_stdLattice_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
private lemma mem_stdLattice_iff_eq
  {d : ℕ}
  {x : Fin d → ℝ} :
-- imply
  x ∈ stdLattice d ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
-- proof
  apply LatticePointEnumerator.mem_stdLattice_iff

/--
[zero_mem_stdLattice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
private lemma zero_mem_stdLattice_eq
  {d : ℕ} :
-- imply
  (0 : Fin d → ℝ) ∈ stdLattice d := by
-- proof
  apply LatticePointEnumerator.zero_mem_stdLattice d

/--
[latticeEnumerator_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
private lemma latticeEnumerator_empty_eq
  {d : ℕ}
  {t : ℝ} :
-- imply
  latticeEnumerator d ∅ t = 0 := by
-- proof
  apply LatticePointEnumerator.latticeEnumerator_empty d t

/--
[translatedLatticeEnumerator_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
private lemma translatedLatticeEnumerator_empty_eq
  {d : ℕ}
  {t : ℝ}
  {x : Fin d → ℝ} :
-- imply
  translatedLatticeEnumerator d ∅ t x = 0 := by
-- proof
  apply LatticePointEnumerator.translatedLatticeEnumerator_empty d t x

/--
[finite_latticePointSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
private lemma finite_latticePointSet_eq
  {d : ℕ}
  {P : Set (Fin d → ℝ)}
  {t : ℝ}
-- given
  (hb : Bornology.IsBounded P) :
-- imply
  Set.Finite (latticePointSet d P t) := by
-- proof
  apply LatticePointEnumerator.finite_latticePointSet d P t hb

/--
[finite_latticePointSetPos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
private lemma finite_latticePointSetPos_eq
  {d : ℕ}
  {P : Set (Fin d → ℝ)}
  {t : {t : ℝ // 0 < t}}
-- given
  (hb : Bornology.IsBounded P) :
-- imply
  Set.Finite (latticePointSetPos d P t) := by
-- proof
  apply LatticePointEnumerator.finite_latticePointSetPos d P t hb

/--
[finite_translatedLatticePointSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
private lemma finite_translatedLatticePointSet_eq
  {d : ℕ}
  {P : Set (Fin d → ℝ)}
  {t : ℝ}
  {x : Fin d → ℝ}
-- given
  (hb : Bornology.IsBounded P) :
-- imply
  Set.Finite (translatedLatticePointSet d P t x) := by
-- proof
  apply LatticePointEnumerator.finite_translatedLatticePointSet d P t x hb

/--
[finite_translatedLatticePointSetPos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
private lemma finite_translatedLatticePointSetPos_eq
  {d : ℕ}
  {P : Set (Fin d → ℝ)}
  {t : {t : ℝ // 0 < t}}
  {x : Fin d → ℝ}
-- given
  (hb : Bornology.IsBounded P) :
-- imply
  Set.Finite (translatedLatticePointSetPos d P t x) := by
-- proof
  apply LatticePointEnumerator.finite_translatedLatticePointSetPos d P t x hb


-- created on 2026-10-20
