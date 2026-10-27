import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RepresentationTheory.Homological.TateCohomology.FiniteCyclic.Part4
open CategoryTheory Limits ModuleCat Rep
open TateCohomology


namespace TateCohomology

/--
[nonempty_periodicityIso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean)
-/
@[path]
private lemma nonempty_periodicityIso
  [CommGroup G]
  {R G : Type u} [CommRing R] [Group G] [Fintype G] [IsCyclic G]
  {A : Rep R G}
  {n : ℤ} :
-- imply
  Nonempty (tateCohomology A n ≅ tateCohomology A (n + 2)) := by
-- proof
  let _ : CommGroup G := IsCyclic.commGroup
  let _ : DecidableEq G := Classical.decEq G
  let g : G := (IsCyclic.exists_generator (α := G)).choose
  have hg : ∀ x, x ∈ Subgroup.zpowers g :=
    (IsCyclic.exists_generator (α := G)).choose_spec
  refine ⟨?_⟩
  cases n with
  | ofNat i =>
    cases i with
    | zero => simpa using zeroPeriodicityIso A g hg
    | succ i =>
      letI : NeZero (i + 1) := ⟨by omega⟩
      simpa using positivePeriodicityIso A g hg (i + 1)
  | negSucc i =>
    cases i with
    | zero => simpa using negOnePeriodicityIso A g hg
    | succ i =>
      cases i with
      | zero => simpa using negTwoPeriodicityIso A g hg
      | succ i =>
        cases i with
        | zero => simpa using negThreePeriodicityIso A g hg
        | succ i =>
          convert negativePeriodicityIso A g hg i using 1 <;>
            simp [Int.negSucc_eq] <;> ring_nf

end TateCohomology


-- created on 2026-10-20
-- updated on 2026-10-26
