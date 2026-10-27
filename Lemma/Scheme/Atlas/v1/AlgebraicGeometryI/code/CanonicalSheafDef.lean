import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef.Part2
open KaehlerDifferential CanonicalSheafDef


namespace CanonicalSheafDef

/--
[smooth_relDim_rank_kaehler](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean)
-/
@[path]
lemma smooth_relDim_rank_kaehler
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [Nontrivial S]
  {n : ℕ}
  [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
-- imply
  Module.rank S (Ω[S⁄R]) = n :=
-- proof
  Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n

end CanonicalSheafDef

namespace CanonicalSheafDef

/--
[smooth_kaehler_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean)
-/
@[path]
lemma smooth_kaehler_free
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [Algebra.IsStandardSmooth R S] :
-- imply
  Module.Free S (Ω[S⁄R]) :=
-- proof
  Algebra.IsStandardSmooth.free_kaehlerDifferential

end CanonicalSheafDef

namespace CanonicalSheafDef

/--
[canonicalModule_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean)
-/
@[path]
lemma canonicalModule_free
  {k : Type u}
  {A : Type v}
  [CommRing k]
  [CommRing A]
  [Algebra k A]
  {d : ℕ}
  [h : IsSmoothOfDimension k A d] :
-- imply
  Module.Free A (↥(canonicalModule k A d)) := by
-- proof
  haveI := h.free
  haveI := h.finite
  show Module.Free A ↥(⋀[A]^d (Ω[A⁄k]))
  exact inferInstance

end CanonicalSheafDef

namespace CanonicalSheafDef

/--
[canonicalModule_finrank_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean)
-/
@[path]
lemma canonicalModule_finrank_eq_one
  {k : Type u}
  {A : Type v}
  [CommRing k]
  [CommRing A]
  [Algebra k A]
  [Nontrivial A]
  {d : ℕ}
  [h : IsSmoothOfDimension k A d] :
-- imply
  Module.finrank A (↥(canonicalModule k A d)) = 1 := by
-- proof
  haveI := h.free
  haveI := h.finite
  show Module.finrank A ↥(⋀[A]^d (Ω[A⁄k])) = 1
  rw [exteriorPower.finrank_eq, h.finrank_eq, Nat.choose_self]

end CanonicalSheafDef

namespace CanonicalSheafDef

/--
[conormalModule_isNoetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean)
-/
@[path]
lemma conormalModule_isNoetherian
  {A : Type u}
  [CommRing A]
  [IsNoetherianRing A]
  {I : Ideal A} :
-- imply
  IsNoetherian A (conormalModule A I) := by
-- proof
  change IsNoetherian A (↥I ⧸ (I • ⊤ : Submodule A ↥I))
  exact isNoetherian_quotient _

end CanonicalSheafDef

namespace CanonicalSheafDef

/--
[conormalModule_finite_of_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean)
-/
@[path]
lemma conormalModule_finite_of_noetherian
  {A : Type u}
  [CommRing A]
  [IsNoetherianRing A]
  {I : Ideal A} :
-- imply
  Module.Finite A (conormalModule A I) := by
-- proof
  haveI := conormalModule_isNoetherian A I
  infer_instance
end CanonicalSheafDef



-- created on 2026-10-23
