import Mathlib
import sympy.Basic
import Def.Geometry.LatticePointEnumerator
open scoped Pointwise
open LatticePointEnumerator


namespace LatticePointEnumerator

/--
[mem_stdLattice_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
lemma mem_stdLattice_iff
  {d : ℕ}
  {x : Fin d → ℝ} :
-- imply
  x ∈ stdLattice d ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
-- proof
  unfold stdLattice
  rw [(Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ x]
  simp [Pi.basisFun_repr]

end LatticePointEnumerator

namespace LatticePointEnumerator

/--
[zero_mem_stdLattice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
lemma zero_mem_stdLattice
  {d : ℕ} :
-- imply
  (0 : Fin d → ℝ) ∈ stdLattice d :=
-- proof
  Submodule.zero_mem _

end LatticePointEnumerator

namespace LatticePointEnumerator

/--
[latticeEnumerator_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
lemma latticeEnumerator_empty
  {d : ℕ}
  {t : ℝ} :
-- imply
  latticeEnumerator d ∅ t = 0 := by
-- proof
  simp [latticeEnumerator, latticePointSet]

end LatticePointEnumerator

namespace LatticePointEnumerator

/--
[translatedLatticeEnumerator_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
lemma translatedLatticeEnumerator_empty
  {d : ℕ}
  {t : ℝ}
  {x : Fin d → ℝ} :
-- imply
  translatedLatticeEnumerator d ∅ t x = 0 := by
-- proof
  simp [translatedLatticeEnumerator, translatedLatticePointSet]

end LatticePointEnumerator

namespace LatticePointEnumerator

/--
[finite_latticePointSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
lemma finite_latticePointSet
  {d : ℕ}
  {P : Set (Fin d → ℝ)}
  {t : ℝ}
-- given
  (hb : Bornology.IsBounded P) :
-- imply
  Set.Finite (latticePointSet d P t) := by
-- proof
  unfold latticePointSet stdLattice
  exact ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin d)) (hb.smul₀ t)

end LatticePointEnumerator

namespace LatticePointEnumerator

/--
[finite_latticePointSetPos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
lemma finite_latticePointSetPos
  {d : ℕ}
  {P : Set (Fin d → ℝ)}
  {t : {t : ℝ // 0 < t}}
-- given
  (hb : Bornology.IsBounded P) :
-- imply
  Set.Finite (latticePointSetPos d P t) :=
-- proof
  finite_latticePointSet d P t.val hb

end LatticePointEnumerator

namespace LatticePointEnumerator

/--
[finite_translatedLatticePointSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
lemma finite_translatedLatticePointSet
  {d : ℕ}
  {P : Set (Fin d → ℝ)}
  {t : ℝ}
  {x : Fin d → ℝ}
-- given
  (hb : Bornology.IsBounded P) :
-- imply
  Set.Finite (translatedLatticePointSet d P t x) := by
-- proof
  unfold translatedLatticePointSet stdLattice
  exact ZSpan.setFinite_inter _ ((hb.smul₀ t).add (Set.finite_singleton x).isBounded)

end LatticePointEnumerator

namespace LatticePointEnumerator

/--
[finite_translatedLatticePointSetPos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean)
-/
@[path]
lemma finite_translatedLatticePointSetPos
  {d : ℕ}
  {P : Set (Fin d → ℝ)}
  {t : {t : ℝ // 0 < t}}
  {x : Fin d → ℝ}
-- given
  (hb : Bornology.IsBounded P) :
-- imply
  Set.Finite (translatedLatticePointSetPos d P t x) :=
-- proof
  finite_translatedLatticePointSet d P t.val x hb

end LatticePointEnumerator


-- created on 2026-10-20
-- updated on 2026-10-23
