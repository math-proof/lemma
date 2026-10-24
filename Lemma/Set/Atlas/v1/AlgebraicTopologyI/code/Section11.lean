import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section11
open Set Topology MayerVietoris
open Function


/--
[isCover_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean)
-/
@[path]
lemma isCover_iff
  [TopologicalSpace X]
  {𝒜 : Set (Set X)} :
-- imply
  IsCover 𝒜 ↔ ∀ x : X, ∃ A ∈ 𝒜, x ∈ interior A := by
-- proof
  simp [IsCover, Set.eq_univ_iff_forall]
namespace AlgebraicTopologyI

namespace MayerVietoris

/--
[exact_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean)
-/
@[path]
lemma exact_sequence
  [TopologicalSpace X]
  [AddCommGroup Aprev]
  [AddCommGroup Bprev]
  [AddCommGroup Bprev']
  [AddCommGroup C]
  [AddCommGroup C']
  [AddCommGroup A]
  [AddCommGroup A']
  [AddCommGroup B]
  [AddCommGroup B']
  [AddCommGroup Cnext']
  {jprev : Aprev →+ Bprev}
  {dprev : Bprev →+ C}
  {k : C →+ A}
  {j : A →+ B}
  {d'prev : Bprev' →+ C'}
  {k' : C' →+ A'}
  {j' : A' →+ B'}
  {d'next : B' →+ Cnext'}
  {gprev : Bprev' ≃+ Bprev}
  {f : A' →+ A}
  {g : B' ≃+ B}
  {exact_jprev_dprev : Exact jprev dprev}
  {exact_dprev_k : Exact dprev k}
  {exact_k_j : Exact k j}
  {exact_d'prev_k' : Exact d'prev k'}
  {exact_k'_j' : Exact k' j'}
  {exact_j'_d'next : Exact j' d'next}
-- given
  (h : C' →+ C)
  (comm_kh : ∀ x, k (h x) = f (k' x))
  (comm_jf : ∀ x, j (f x) = g (j' x))
  (comm_dg : ∀ x, dprev (gprev x) = h (d'prev x)) :
-- imply
  Exact (fun x : C' => (h x, -k' x) : C' → C × A') (fun p : C × A' => k p.1 + f p.2 : C × A' → A) ∧ Exact (fun p : C × A' => k p.1 + f p.2) (fun a : A => d'next (g.symm (j a))) ∧ Exact (fun a : Aprev => d'prev (gprev.symm (jprev a))) (fun x : C' => (h x, -k' x) : C' → C × A') :=
-- proof
  ⟨exact_at_prod k j k' j' h f g dprev d'prev gprev
    exact_k_j exact_k'_j' exact_dprev_k exact_d'prev_k'
    comm_kh comm_jf comm_dg,
    exact_at_A k j j' d'next f g exact_k_j exact_j'_d'next comm_jf,
    exact_at_C' jprev dprev k' d'prev h gprev
      exact_jprev_dprev exact_d'prev_k' comm_dg⟩

end MayerVietoris

/--
[exact_at_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean)
-/
@[path]
private lemma exact_at_prod_eq
  [TopologicalSpace X]
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  [AddCommGroup A']
  [AddCommGroup B']
  [AddCommGroup C']
  [AddCommGroup Bprev]
  [AddCommGroup Bprev']
  {k : C →+ A}
  {j : A →+ B}
  {k' : C' →+ A'}
  {j' : A' →+ B'}
  {f : A' →+ A}
  {g : B' ≃+ B}
  {dprev : Bprev →+ C}
  {d'prev : Bprev' →+ C'}
  {gprev : Bprev' ≃+ Bprev}
  {exact_A_top : Exact k j}
  {exact_A'_bot : Exact k' j'}
  {exact_C_top : Exact dprev k}
  {exact_C'_bot : Exact d'prev k'}
-- given
  (h : C' →+ C)
  (comm1 : ∀ x, k (h x) = f (k' x))
  (comm2 : ∀ x, j (f x) = g (j' x))
  (comm_prev : ∀ x, dprev (gprev x) = h (d'prev x)) :
-- imply
  Exact (fun x : C' => (h x, -k' x) : C' → C × A') (fun p : C × A' => k p.1 + f p.2 : C × A' → A) := by
-- proof
  apply MayerVietoris.exact_at_prod k j k' j' h f g dprev d'prev gprev exact_A_top exact_A'_bot exact_C_top exact_C'_bot comm1 comm2 comm_prev

/--
[exact_at_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean)
-/
@[path]
private lemma exact_at_A_eq
  [TopologicalSpace X]
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  [AddCommGroup A']
  [AddCommGroup B']
  [AddCommGroup C₂']
  {k : C →+ A}
  {j : A →+ B}
  {j' : A' →+ B'}
  {d' : B' →+ C₂'}
  {f : A' →+ A}
  {g : B' ≃+ B}
  {exact_A_top : Exact k j}
  {exact_B'_bot : Exact j' d'}
-- given
  (comm2 : ∀ x, j (f x) = g (j' x)) :
-- imply
  Exact (fun p : C × A' => k p.1 + f p.2) (fun a : A => d' (g.symm (j a))) := by
-- proof
  apply MayerVietoris.exact_at_A k j j' d' f g exact_A_top exact_B'_bot comm2

/--
[exact_at_C'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean)
-/
@[path]
private lemma exact_at_C'_eq
  [TopologicalSpace X]
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  [AddCommGroup A']
  [AddCommGroup B']
  [AddCommGroup C']
  {j : A →+ B}
  {dtop : B →+ C}
  {k' : C' →+ A'}
  {d' : B' →+ C'}
  {g : B' ≃+ B}
  {exact_B_top : Exact j dtop}
  {exact_C'_bot : Exact d' k'}
-- given
  (h : C' →+ C)
  (comm3 : ∀ x, dtop (g x) = h (d' x)) :
-- imply
  Exact (fun a : A => d' (g.symm (j a))) (fun x : C' => (h x, -k' x) : C' → C × A') := by
-- proof
  apply MayerVietoris.exact_at_C' j dtop k' d' h g exact_B_top exact_C'_bot comm3


-- created on 2026-10-23
