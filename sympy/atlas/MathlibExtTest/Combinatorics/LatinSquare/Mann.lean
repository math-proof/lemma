/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/LatinSquare/Mann.lean -/


import Lemma.Finset.LatinSquare.Mann

namespace MetaMathlibExt

/-- The public criterion can be applied directly to any pair of Latin squares. -/
example {n : ℕ} (A B : Fin n → Fin n → Fin n)
    (hArow : ∀ i, Function.Bijective (A i))
    (hAcol : ∀ j, Function.Bijective (fun i => A i j))
    (hBrow : ∀ i, Function.Bijective (B i))
    (hBcol : ∀ j, Function.Bijective (fun i => B i j)) :
    Function.Bijective (fun ij : Fin n × Fin n => (A ij.1 ij.2, B ij.1 ij.2)) ↔
      ((∀ i, Function.Bijective
          (fun j => A i ((Equiv.ofBijective (B i) (hBrow i)).symm j))) ∧
        ∀ j, Function.Bijective
          (fun i => A i ((Equiv.ofBijective (B i) (hBrow i)).symm j))) :=
  mann_product_criterion_for_orthogonal_latin_squares A B hArow hAcol hBrow hBcol

end MetaMathlibExt
