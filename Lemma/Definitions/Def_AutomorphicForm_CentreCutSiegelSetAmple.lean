import Lemma.Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Lemma.Definitions.Def_NumberField_SiegelVolume

set_option autoImplicit false

open MeasureTheory Set IsDedekindDomain NumberField Metric

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicCentre NumberField.SiegelVolume

variable (F : Type) [Field F] [NumberField F]

def centreCutSiegelSetAmple (c u d₁ d₂ κ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | g ∈ centreCutSiegelSet F c u d₁ d₂ ∧
    ∀ w w' : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
        κ * localHeight (archComponent F w' (glArch (𝓞 F) F g))}

variable {F}

theorem mem_centreCutSiegelSetAmple_iff {c u d₁ d₂ κ : ℝ} {g : AdelicGL2 (𝓞 F) F} :
    g ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ ↔
      g ∈ centreCutSiegelSet F c u d₁ d₂ ∧
        ∀ w w' : InfinitePlace F,
          localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
            κ * localHeight (archComponent F w' (glArch (𝓞 F) F g)) :=
  Iff.rfl

theorem centreCutSiegelSetAmple_subset (c u d₁ d₂ κ : ℝ) :
    centreCutSiegelSetAmple F c u d₁ d₂ κ ⊆ centreCutSiegelSet F c u d₁ d₂ :=
  fun _ hg => hg.1

theorem centreCutSiegelSetAmple_mono {c u d₁ d₂ κ κ' : ℝ} (h : κ ≤ κ') :
    centreCutSiegelSetAmple F c u d₁ d₂ κ ⊆ centreCutSiegelSetAmple F c u d₁ d₂ κ' :=
  fun _ hg => ⟨hg.1, fun w w' => (hg.2 w w').trans
    (mul_le_mul_of_nonneg_right h (localHeight_pos _).le)⟩

theorem centreCutSiegelSetAmple_eq_of_subsingleton [Subsingleton (InfinitePlace F)] {c u d₁ d₂ κ : ℝ}
    (hκ : 1 ≤ κ) : centreCutSiegelSetAmple F c u d₁ d₂ κ = centreCutSiegelSet F c u d₁ d₂ := by
  refine Subset.antisymm (centreCutSiegelSetAmple_subset c u d₁ d₂ κ) fun g hg => ⟨hg, fun w w' => ?_⟩
  rw [Subsingleton.elim w' w]
  exact le_mul_of_one_le_left (localHeight_pos _).le hκ

theorem localHeight_le_mul_self {κ : ℝ} (hκ : 1 ≤ κ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
      κ * localHeight (archComponent F w (glArch (𝓞 F) F g)) :=
  le_mul_of_one_le_left (localHeight_pos _).le hκ

theorem one_mem_centreCutSiegelSetAmple {c u d₁ d₂ κ : ℝ} (hc : c ≤ 1) (hd₁ : d₁ ≤ 1) (hd₂ : 1 ≤ d₂)
    (hκ : 1 ≤ κ) : (1 : AdelicGL2 (𝓞 F) F) ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ := by
  refine ⟨one_mem_centreCutSiegelSet hc hd₁ hd₂, fun w w' => ?_⟩
  rw [map_one, map_one, map_one, localHeight_one, localHeight_one, mul_one]
  exact hκ

theorem isClosed_setOf_localHeight_le_mul (κ : ℝ) (w w' : InfinitePlace F) :
    IsClosed {g : AdelicGL2 (𝓞 F) F |
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
        κ * localHeight (archComponent F w' (glArch (𝓞 F) F g))} :=
  isClosed_le ((continuous_localHeight).comp
      ((continuous_archComponent F w).comp (continuous_glArch (𝓞 F) F)))
    (continuous_const.mul ((continuous_localHeight).comp
      ((continuous_archComponent F w').comp (continuous_glArch (𝓞 F) F))))

theorem centreCutSiegelSetAmple_eq_inter (c u d₁ d₂ κ : ℝ) :
    centreCutSiegelSetAmple F c u d₁ d₂ κ =
      centreCutSiegelSet F c u d₁ d₂ ∩
        ⋂ w : InfinitePlace F, ⋂ w' : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
          localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
            κ * localHeight (archComponent F w' (glArch (𝓞 F) F g))} := by
  ext g
  simp only [mem_centreCutSiegelSetAmple_iff, mem_inter_iff, mem_iInter, mem_setOf_eq]

theorem measurableSet_centreCutSiegelSetAmple {mS : MeasurableSpace (AdelicGL2 (𝓞 F) F)}
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (c u d₁ d₂ κ : ℝ) :
    MeasurableSet (centreCutSiegelSetAmple F c u d₁ d₂ κ) := by
  rw [centreCutSiegelSetAmple_eq_inter]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).inter
    (MeasurableSet.iInter fun w => MeasurableSet.iInter fun w' =>
      (isClosed_setOf_localHeight_le_mul κ w w').measurableSet)

theorem measure_centreCutSiegelSetAmple_lt_top [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ κ : ℝ) :
    μ (centreCutSiegelSetAmple F c u d₁ d₂ κ) < ⊤ :=
  (measure_mono (centreCutSiegelSetAmple_subset c u d₁ d₂ κ)).trans_lt
    (measure_centreCutSiegelSet_lt_top μ hc u hd₁ d₂)

end WindowedSiegel

end AutomorphicForm

end
