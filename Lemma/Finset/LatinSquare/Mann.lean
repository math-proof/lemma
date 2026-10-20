import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.LatinSquare.Mann
open MetaMathlibExt


/--
[mann_product_criterion_for_orthogonal_latin_squares](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/LatinSquare/Mann.lean)
-/
@[path]
private lemma mann_product_criterion_for_orthogonal_latin_squares_eq
  {n : ℕ}
  {A B : Fin n → Fin n → Fin n}
-- given
  (hArow : ∀ i, Function.Bijective (A i))
  (hAcol : ∀ j, Function.Bijective (fun i => A i j))
  (hBrow : ∀ i, Function.Bijective (B i))
  (hBcol : ∀ j, Function.Bijective (fun i => B i j)) :
-- imply
  Function.Bijective (fun ij : Fin n × Fin n => (A ij.1 ij.2, B ij.1 ij.2)) ↔
    ((∀ i, Function.Bijective
    (fun j => A i ((Equiv.ofBijective (B i) (hBrow i)).symm j))) ∧
    ∀ j, Function.Bijective
    (fun i => A i ((Equiv.ofBijective (B i) (hBrow i)).symm j))) := by
-- proof
  apply MetaMathlibExt.mann_product_criterion_for_orthogonal_latin_squares A B hArow hAcol hBrow hBcol


-- created on 2026-10-20
