/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Combinatorics.SimpleGraph.Frucht.Part3


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

noncomputable def fruchtPhi (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) : G → fruchtGraph N e ≃g fruchtGraph N e :=
  fun a => fruchtShiftIso N e a

noncomputable def fruchtHom (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) : G →* fruchtGraph N e ≃g fruchtGraph N e :=
  MonoidHom.mk' (fruchtPhi N e) (fun a b => RelIso.ext fun x =>
    congrArg (fun p : Equiv.Perm (G ⊕ (G × Fin N)) => p x) (fruchtShift_mul N a b))

noncomputable def fruchtMulEquiv (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (hN : 2 ≤ N) : G ≃* fruchtGraph N e ≃g fruchtGraph N e := by
  refine MulEquiv.ofBijective (fruchtHom N e) ?_
  constructor
  · intro a b hab
    have hval2 : fruchtShift N a = fruchtShift N b := congrArg RelIso.toEquiv hab
    have h1 := congrArg (fun p : Equiv.Perm (G ⊕ (G × Fin N)) => p (.inl 1)) hval2
    simp only [fruchtShift_inl, mul_one] at h1
    exact Sum.inl_injective h1
  · intro σ
    obtain ⟨a, ha⟩ := fruchtAut_eq_shift N e hN σ
    exact ⟨a, ha.symm⟩

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
