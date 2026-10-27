import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RamificationYoneda.Part2
open CategoryTheory Opposite Lecture6


namespace Lecture6

/--
[ramificationLocus_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationYoneda.lean)
-/
@[path]
lemma ramificationLocus_isClosed
  {A B : Type*}
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B] :
-- imply
  IsClosed (PrimeSpectrum.zeroLocus (ramificationIdeal A B : Set A)) :=
-- proof
  PrimeSpectrum.isClosed_zeroLocus _

end Lecture6

namespace Lecture6

/--
[ramificationLocus_ne_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationYoneda.lean)
-/
@[path]
lemma ramificationLocus_ne_univ
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B]
-- given
  (hsep : Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0) :
-- imply
  PrimeSpectrum.zeroLocus (ramificationIdeal A B : Set A) ≠ Set.univ := by
-- proof
  intro h
  rw [PrimeSpectrum.zeroLocus_eq_univ_iff] at h
  have hmem : Algebra.discr A (Module.Free.chooseBasis A B) ∈ nilradical A := by
    apply h
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [nilradical_eq_zero] at hmem
  exact hsep hmem

end Lecture6

namespace Lecture6

/--
[discr_ne_zero_of_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationYoneda.lean)
-/
@[path]
lemma discr_ne_zero_of_separable
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Module.Finite K L]
  [Algebra.IsSeparable K L] :
-- imply
  Algebra.discr K (Module.Free.chooseBasis K L) ≠ 0 :=
-- proof
  Algebra.discr_not_zero_of_basis K _

end Lecture6


-- created on 2026-10-23
