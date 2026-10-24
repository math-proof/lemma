import Mathlib
import sympy.Basic
import Lemma.PowerSeries.MemFinsuppAntidiagUnivIffDegree
open MvPolynomial PowerSeries


/--
Atlas `finrank_homogeneousSubmodule_eq'` (Ideal dump carve; SyzygiesKoszul olean broken).

[finrank_homogeneousSubmodule_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  {n d : ℕ} :
-- imply
  Module.finrank k (homogeneousSubmodule (Fin n) k d) = n.multichoose d := by
-- proof
  classical
  let _ : Fintype {s : Finsupp (Fin n) ℕ | Finsupp.degree s = d} :=
    Fintype.ofFinset ((Finset.univ : Finset (Fin n)).finsuppAntidiag d)
      fun f => MemFinsuppAntidiagUnivIffDegree (f := f)
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have e : AddMonoidAlgebra.supported k k {s : Finsupp (Fin n) ℕ | Finsupp.degree s = d} ≃ₗ[k]
    Finsupp {s : Finsupp (Fin n) ℕ | Finsupp.degree s = d} k :=
    AddMonoidAlgebra.supportedEquivFinsupp _
  calc
    _ = Module.finrank k (Finsupp {d_1 : Finsupp (Fin n) ℕ | Finsupp.degree d_1 = d} k) :=
      e.finrank_eq
    _ = Fintype.card {d_1 : Finsupp (Fin n) ℕ | Finsupp.degree d_1 = d} :=
      Module.finrank_finsupp_self k
    _ = ((Finset.univ : Finset (Fin n)).finsuppAntidiag d).card :=
      Fintype.card_ofFinset _ fun f => MemFinsuppAntidiagUnivIffDegree (f := f)
    _ = n.multichoose d := by
      rw [Finset.card_finsuppAntidiag_nat_eq_multichoose]
      simp [Fintype.card_fin]


-- created on 2026-10-24
