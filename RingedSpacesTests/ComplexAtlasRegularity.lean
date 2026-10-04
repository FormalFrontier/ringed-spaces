/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Complex regularity on concrete atlases

A two-dimensional complex space with identity and nontrivial translation charts satisfies
the raw ordered-transition hypothesis directly, on its own atlas. Zero-dimensional and
empty carriers exercise the boundary cases without assuming their conclusions.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace ComplexAtlasRegularityTest

private abbrev Plane := EuclideanSpace ℂ (Fin 2)

private def shift : Plane := EuclideanSpace.single 0 1

private def translatedChart : OpenPartialHomeomorph Plane Plane :=
  (Homeomorph.addLeft shift).toOpenPartialHomeomorph

@[instance_reducible]
private def translatedAtlas : ChartedSpace Plane Plane where
  atlas := {OpenPartialHomeomorph.refl Plane, translatedChart}
  chartAt _ := OpenPartialHomeomorph.refl Plane
  mem_chart_source _ := by simp
  chart_mem_atlas _ := by simp

section Translation

private local instance : ChartedSpace Plane Plane := translatedAtlas

private theorem chart_differentiable {e : OpenPartialHomeomorph Plane Plane}
    (he : e ∈ atlas Plane Plane) : Differentiable ℂ e := by
  change e = OpenPartialHomeomorph.refl Plane ∨ e = translatedChart at he
  rcases he with rfl | rfl
  · change Differentiable ℂ (fun x : Plane => x)
    exact differentiable_id
  · simpa [translatedChart, Homeomorph.addLeft] using
      (differentiable_id.const_add shift)

private theorem chart_symm_differentiable {e : OpenPartialHomeomorph Plane Plane}
    (he : e ∈ atlas Plane Plane) : Differentiable ℂ e.symm := by
  change e = OpenPartialHomeomorph.refl Plane ∨ e = translatedChart at he
  rcases he with rfl | rfl
  · change Differentiable ℂ (fun x : Plane => x)
    exact differentiable_id
  · simpa [translatedChart, Homeomorph.addLeft] using
      (differentiable_id.const_add (-shift))

private theorem translatedAtlas_differentiable :
    ∀ e e' : OpenPartialHomeomorph Plane Plane,
      e ∈ atlas Plane Plane → e' ∈ atlas Plane Plane →
      DifferentiableOn ℂ (𝓘(ℂ, Plane) ∘ (e.symm ≫ₕ e') ∘ 𝓘(ℂ, Plane).symm)
        (𝓘(ℂ, Plane).symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range 𝓘(ℂ, Plane)) := by
  intro e e' he he'
  change DifferentiableOn ℂ (fun x : Plane => e' (e.symm x)) _
  exact ((chart_differentiable he').comp (chart_symm_differentiable he)).differentiableOn

private theorem shift_ne_zero : shift ≠ (0 : Plane) := by
  intro h
  have hzero := congrArg (fun vector : Plane => vector (0 : Fin 2)) h
  simp [shift] at hzero

example : OpenPartialHomeomorph.refl Plane ∈ atlas Plane Plane ∧
    translatedChart ∈ atlas Plane Plane := by
  constructor <;> change _ = OpenPartialHomeomorph.refl Plane ∨ _ = translatedChart
  · exact Or.inl rfl
  · exact Or.inr rfl

example : ((OpenPartialHomeomorph.refl Plane).symm ≫ₕ translatedChart) (0 : Plane) = shift := by
  simp [translatedChart, Homeomorph.addLeft]

example : ((OpenPartialHomeomorph.refl Plane).symm ≫ₕ translatedChart) (0 : Plane) ≠
    (0 : Plane) := by
  simpa [translatedChart, Homeomorph.addLeft]
    using shift_ne_zero

/-- A two-dimensional complex charted space with a genuinely nonidentity atlas transition. -/
theorem exists_nonidentity_transition :
    ∃ (charts : ChartedSpace (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2)))
        (e e' : OpenPartialHomeomorph (EuclideanSpace ℂ (Fin 2))
          (EuclideanSpace ℂ (Fin 2))),
      e ∈ charts.atlas ∧ e' ∈ charts.atlas ∧
        (e.symm ≫ₕ e') (0 : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
  refine ⟨translatedAtlas, OpenPartialHomeomorph.refl Plane, translatedChart,
    ?_, ?_, ?_⟩
  · change OpenPartialHomeomorph.refl Plane = OpenPartialHomeomorph.refl Plane ∨
      OpenPartialHomeomorph.refl Plane = translatedChart
    exact Or.inl rfl
  · change translatedChart = OpenPartialHomeomorph.refl Plane ∨
      translatedChart = translatedChart
    exact Or.inr rfl
  · simpa [translatedChart, Homeomorph.addLeft] using shift_ne_zero

example : IsManifold 𝓘(ℂ, Plane) ω Plane :=
  isManifold_omega_of_differentiableOn_chartTransitions 𝓘(ℂ, Plane)
    translatedAtlas_differentiable

example : IsManifold 𝓘(ℂ, Plane) ∞ Plane :=
  isManifold_infty_of_differentiableOn_chartTransitions 𝓘(ℂ, Plane)
    translatedAtlas_differentiable

end Translation

private abbrev ZeroModel := EuclideanSpace ℂ (Fin 0)

private theorem zeroModel_differentiable :
    ∀ e e' : OpenPartialHomeomorph ZeroModel ZeroModel,
      e ∈ atlas ZeroModel ZeroModel → e' ∈ atlas ZeroModel ZeroModel →
      DifferentiableOn ℂ (𝓘(ℂ, ZeroModel) ∘ (e.symm ≫ₕ e') ∘ 𝓘(ℂ, ZeroModel).symm)
        (𝓘(ℂ, ZeroModel).symm ⁻¹' (e.symm ≫ₕ e').source ∩
          Set.range 𝓘(ℂ, ZeroModel)) := by
  intro e e' he he'
  rw [chartedSpaceSelf_atlas] at he he'
  subst e
  subst e'
  change DifferentiableOn ℂ (fun x : ZeroModel => x) _
  exact differentiable_id.differentiableOn

example : Nonempty ZeroModel := ⟨0⟩

example : IsManifold 𝓘(ℂ, ZeroModel) ω ZeroModel :=
  isManifold_omega_of_differentiableOn_chartTransitions 𝓘(ℂ, ZeroModel)
    zeroModel_differentiable

example : IsManifold 𝓘(ℂ, Plane) ω Plane := by
  exact isManifold_omega_of_isManifold_one (I := 𝓘(ℂ, Plane))

universe u v

private local instance emptyChartedSpace (H : Type v) [TopologicalSpace H] :
    ChartedSpace H Empty := ChartedSpace.empty H Empty

private theorem empty_differentiable :
    ∀ e e' : OpenPartialHomeomorph Empty ℂ,
      e ∈ atlas ℂ Empty → e' ∈ atlas ℂ Empty →
      DifferentiableOn ℂ (𝓘(ℂ) ∘ (e.symm ≫ₕ e') ∘ 𝓘(ℂ).symm)
        (𝓘(ℂ).symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range 𝓘(ℂ)) := by
  intro e e' he
  change e ∈ (∅ : Set (OpenPartialHomeomorph Empty ℂ)) at he
  simp at he

example : IsManifold 𝓘(ℂ) ω Empty :=
  isManifold_omega_of_differentiableOn_chartTransitions 𝓘(ℂ) empty_differentiable

example {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℂ E H) [I.Boundaryless] : IsManifold I ω Empty := by
  apply isManifold_omega_of_differentiableOn_chartTransitions I
  intro e e' he
  change e ∈ (∅ : Set (OpenPartialHomeomorph Empty H)) at he
  simp at he

end ComplexAtlasRegularityTest
