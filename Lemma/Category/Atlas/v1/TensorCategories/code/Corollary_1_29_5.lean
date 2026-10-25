import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TensorCategories.code.TaftWilsonComponentGrouplike
open Coalgebra
open scoped TensorProduct


/--
[Corollary_1_29_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_29_5.lean)
-/
@[path]
lemma Corollary_1_29_5
  {R : Type u}
  {C : Type v}
  [Field R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
-- given
  (hPointed : IsPointedCoalgebra (R := R) (C := C)) :
-- imply
  (coradical (R := R) (C := C) = ⨆ (g : C) (_ : g ∈ grouplikes (R := R) (C := C)), Submodule.span R {g}) ∧ (coradicalFiltration (R := R) (C := C) 1 = coradical ⊔ ⨆ (g : C) (_ : g ∈ grouplikes (R := R) (C := C)) (h : C) (_ : h ∈ grouplikes (R := R) (C := C)), skewPrimitiveSpace g h) ∧ (iSupIndep (fun (p : {g : C // g ∈ grouplikes (R := R) (C := C)} × {h : C // h ∈ grouplikes (R := R) (C := C)}) => Submodule.map (coradical (R := R) (C := C)).mkQ (skewPrimitiveSpace p.1.1 p.2.1))) :=
-- proof
  ⟨taftWilson_coradical_eq_span_grouplikes R C hPointed,
    taftWilson_C1_eq R C hPointed,
    taftWilson_directness hPointed⟩


-- created on 2026-10-23
