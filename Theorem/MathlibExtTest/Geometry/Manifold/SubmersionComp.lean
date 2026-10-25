/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Manifold/SubmersionComp.lean -/


import Def.Geometry.Manifold.SubmersionComp
import Lemma.Set.Manifold.SubmersionComp
open scoped ContDiff Manifold Topology
open Manifold


noncomputable section

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E E' E'' F F₁ F₂ : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

variable {H G G' : Type*}
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {J' : ModelWithCorners 𝕜 E'' G'}

variable {M N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G' N']

variable {n : ℕ∞ω} {f : M → N} {g : N → N'} {x : M}

variable [CompleteSpace E] [CompleteSpace E'] [CompleteSpace E'']

variable [I.Boundaryless] [J.Boundaryless] [J'.Boundaryless]

variable [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']

-- Composition is a submersion throughout a neighborhood of the source point.
example (hf : IsSubmersionAt I J n f x) (hg : IsSubmersionAt J J' n g (f x)) :
    ∀ᶠ y in 𝓝 x, IsSubmersionAt I J' n (g ∘ f) y :=
  isOpen_isSubmersionAt.mem_nhds (hg.comp hf)

-- A composed pointwise submersion is smooth at the source point.
example (hf : IsSubmersionAt I J n f x) (hg : IsSubmersionAt J J' n g (f x)) :
    ContMDiffAt I J' n (g ∘ f) x :=
  (hg.comp hf).contMDiffAt

-- Swapping the product complement gives the caller's requested factor order.
example (hf : IsSubmersionOfComplement F₁ I J n f)
    (hg : IsSubmersionOfComplement F₂ J J' n g) :
    IsSubmersionOfComplement (F₁ × F₂) I J' n (g ∘ f) :=
  (hg.comp hf).trans_F (ContinuousLinearEquiv.prodComm 𝕜 F₂ F₁)

section Products

variable {E₁ E₁' E₁'' E₂ E₂' E₂'' : Type u}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₁'] [NormedSpace 𝕜 E₁']
  [NormedAddCommGroup E₁''] [NormedSpace 𝕜 E₁'']
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₂'] [NormedSpace 𝕜 E₂']
  [NormedAddCommGroup E₂''] [NormedSpace 𝕜 E₂'']

variable {H₁ G₁ G₁' H₂ G₂ G₂' : Type*}
  [TopologicalSpace H₁] [TopologicalSpace G₁] [TopologicalSpace G₁']
  [TopologicalSpace H₂] [TopologicalSpace G₂] [TopologicalSpace G₂']

variable {I₁ : ModelWithCorners 𝕜 E₁ H₁} {J₁ : ModelWithCorners 𝕜 E₁' G₁}
  {J₁' : ModelWithCorners 𝕜 E₁'' G₁'} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {J₂ : ModelWithCorners 𝕜 E₂' G₂} {J₂' : ModelWithCorners 𝕜 E₂'' G₂'}

variable {M₁ N₁ N₁' M₂ N₂ N₂' : Type*}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace N₁] [ChartedSpace G₁ N₁]
  [TopologicalSpace N₁'] [ChartedSpace G₁' N₁']
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace N₂] [ChartedSpace G₂ N₂]
  [TopologicalSpace N₂'] [ChartedSpace G₂' N₂']

variable {f₁ : M₁ → N₁} {g₁ : N₁ → N₁'} {x₁ : M₁}
  {f₂ : M₂ → N₂} {g₂ : N₂ → N₂'} {x₂ : M₂}

variable [I₁.Boundaryless] [J₁.Boundaryless] [I₂.Boundaryless] [J₂.Boundaryless]

variable [IsManifold I₁ n M₁] [IsManifold J₁ n N₁] [IsManifold J₁' n N₁']
  [IsManifold I₂ n M₂] [IsManifold J₂ n N₂] [IsManifold J₂' n N₂']

-- Product submersions compose using the boundaryless product models.
example (hf₁ : IsSubmersionAt I₁ J₁ n f₁ x₁)
    (hg₁ : IsSubmersionAt J₁ J₁' n g₁ (f₁ x₁))
    (hf₂ : IsSubmersionAt I₂ J₂ n f₂ x₂)
    (hg₂ : IsSubmersionAt J₂ J₂' n g₂ (f₂ x₂)) :
    IsSubmersionAt (I₁.prod I₂) (J₁'.prod J₂') n
      (Prod.map (g₁ ∘ f₁) (g₂ ∘ f₂)) (x₁, x₂) := by
  have hcomp :=
    (hg₁.prodMap hg₂).comp (f := Prod.map f₁ f₂) (hf₁.prodMap hf₂)
  have hmap : Prod.map g₁ g₂ ∘ Prod.map f₁ f₂ =
      Prod.map (g₁ ∘ f₁) (g₂ ∘ f₂) := by
    funext y
    rcases y with ⟨y₁, y₂⟩
    rfl
  rw [hmap] at hcomp
  exact hcomp

end Products

-- The preferred codomain chart preserves the projection normal form on the new target.
example (hf : IsSubmersionAtOfComplement F I J n f x) :
    ∃ domChart : OpenPartialHomeomorph M H,
      x ∈ domChart.source ∧
      Set.EqOn ((extChartAt J (f x)) ∘ f ∘ (domChart.extend I).symm)
        (Prod.fst ∘ hf.equiv) (domChart.extend I).target := by
  obtain ⟨domChart, hx, _, _, hwritten⟩ :=
    hf.exists_domChart_of_codChart (chartAt G (f x)) (by simp)
      (IsManifold.chart_mem_maximalAtlas (I := J) (f x))
  refine ⟨domChart, hx, ?_⟩
  simpa only [extChartAt] using hwritten

-- The frozen global composition theorem makes the composite globally smooth.
example (hf : IsSubmersion I J n f) (hg : IsSubmersion J J' n g) :
    ContMDiff I J' n (g ∘ f) :=
  IsSubmersion.contMDiff
    (MathlibExt.Geometry.Manifold.SubmersionCompWanted.submersion_comp hf hg)

end
