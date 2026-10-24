import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris
open Set Topology EilenbergSteenrod Function MayerVietoris


namespace MayerVietoris

/--
[MayerVietorisCover.excisive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.excisive
  {c : MayerVietorisCover} :
-- imply
  IsExcisiveTriple c.pairXA (c.Bᶜ) where sub_mem := by
-- proof
  intro x hx
  have hmem := Set.eq_univ_iff_forall.mp c.cover x
  exact hmem.elim (fun h => interior_subset h) (fun hB => absurd (interior_subset hB) hx)
  closure_sub_interior := by
    rw [closure_compl]
    intro x hx
    simp only [Set.mem_compl_iff] at hx
    exact (Set.eq_univ_iff_forall.mp c.cover x).resolve_right hx

end MayerVietoris

namespace MayerVietoris

/--
[MayerVietorisCover.trSub_comp_inv_htpy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.trSub_comp_inv_htpy
  {c : MayerVietorisCover} :
-- imply
  AreHomotopic (c.trSub.comp c.trSubInv) (MapOfPairs.id c.pairAB) :=
-- proof
  ⟨constHomotopy _ (fun x => by simp [MapOfPairs.comp, trSub, trSubInv])⟩

end MayerVietoris

namespace MayerVietoris

/--
[MayerVietorisCover.trSubInv_comp_htpy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.trSubInv_comp_htpy
  {c : MayerVietorisCover} :
-- imply
  AreHomotopic (c.trSubInv.comp c.trSub) (MapOfPairs.id c.EP.subPair) :=
-- proof
  ⟨constHomotopy _ (fun x => by simp [MapOfPairs.comp, trSub, trSubInv])⟩

end MayerVietoris

namespace MayerVietoris

/--
[MayerVietorisCover.trSp_comp_inv_htpy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.trSp_comp_inv_htpy
  {c : MayerVietorisCover} :
-- imply
  AreHomotopic (c.trSp.comp c.trSpInv) (MapOfPairs.id c.pairB) :=
-- proof
  ⟨constHomotopy _ (fun x => by simp [MapOfPairs.comp, trSp, trSpInv])⟩

end MayerVietoris

namespace MayerVietoris

/--
[MayerVietorisCover.trSpInv_comp_htpy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.trSpInv_comp_htpy
  {c : MayerVietorisCover} :
-- imply
  AreHomotopic (c.trSpInv.comp c.trSp) (MapOfPairs.id (TopPair.ofSpace c.EP.space)) :=
-- proof
  ⟨constHomotopy _ (fun x => by simp [MapOfPairs.comp, trSp, trSpInv])⟩

end MayerVietoris

namespace MayerVietoris

/--
[MayerVietorisCover.inclA_X_comp_inclAB_A_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.inclA_X_comp_inclAB_A_eq
  {c : MayerVietorisCover} :
-- imply
  c.inclA_X.comp c.inclAB_A = c.inclB_X.comp c.inclAB_B :=
-- proof
  rfl

end MayerVietoris

namespace MayerVietoris

/--
[MayerVietorisCover.inclAB_B_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.inclAB_B_comp_eq
  {c : MayerVietorisCover} :
-- imply
  c.trSp.comp ((inclusionSubToSpace c.EP).comp c.trSubInv) = c.inclAB_B :=
-- proof
  rfl

end MayerVietoris

namespace MayerVietoris

/--
[MayerVietorisCover.exc_restrictToSub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.exc_restrictToSub_eq
  {c : MayerVietorisCover} :
-- imply
  (excisionInclusion c.pairXA c.Bᶜ).restrictToSub = c.inclAB_A.comp c.trSub :=
-- proof
  rfl

end MayerVietoris

namespace MayerVietoris

/--
[MayerVietorisCover.comm2_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
lemma MayerVietorisCover.comm2_eq
  {c : MayerVietorisCover} :
-- imply
  (inclusionSpaceToPair c.pairXA).comp c.inclB_X = (excisionInclusion c.pairXA c.Bᶜ).comp ((inclusionSpaceToPair c.EP).comp c.trSpInv) :=
-- proof
  rfl

end MayerVietoris

/--
[hom_inv_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
private lemma hom_inv_id_eq
  {n : ℤ}
  {P Q : TopPair}
  {f : MapOfPairs P Q}
  {g : MapOfPairs Q P}
-- given
  (ht : HomologyTheory)
  (hgf : AreHomotopic (g.comp f) (MapOfPairs.id P)) :
-- imply
  ∀ x, (ht.map n g) ((ht.map n f) x) = x := by
-- proof
  apply MayerVietoris.hom_inv_id ht n f g hgf

/--
[transfer_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
private lemma transfer_bijective_eq
  {n : ℤ}
  {P Q : TopPair}
  {f : MapOfPairs P Q}
  {g : MapOfPairs Q P}
-- given
  (ht : HomologyTheory)
  (hfg : AreHomotopic (f.comp g) (MapOfPairs.id Q))
  (hgf : AreHomotopic (g.comp f) (MapOfPairs.id P)) :
-- imply
  Bijective (ht.map n f) := by
-- proof
  apply MayerVietoris.transfer_bijective ht n f g hfg hgf

/--
[exact_transfer_bij](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean)
-/
@[path]
private lemma exact_transfer_bij_eq
  [AddCommGroup B]
  [AddCommGroup C]
  [AddCommGroup B']
  [AddCommGroup C']
  {f : A → B}
  {g : B → C}
  {ψ : B →+ B'}
  {ψ' : B' →+ B}
  {χ : C →+ C'}
-- given
  (he : Exact f g)
  (hψψ' : ∀ y, ψ (ψ' y) = y)
  (hψ'ψ : ∀ x, ψ' (ψ x) = x)
  (hχ_inj : Injective χ) :
-- imply
  Exact (ψ ∘ f) (fun y' => χ (g (ψ' y'))) := by
-- proof
  apply MayerVietoris.exact_transfer_bij he ψ ψ' hψψ' hψ'ψ χ hχ_inj


-- created on 2026-10-23
