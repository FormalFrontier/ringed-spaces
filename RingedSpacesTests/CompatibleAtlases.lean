/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.ChartedSpace.CompatibleAtlases
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Two genuinely different compatible charts

The preferred charts on `ℝ × ℝ` are the identity and a global triangular polynomial shear.
The groupoid hypothesis is verified from the polynomial maps. The comparison theorems give
regularity, equal maximal atlases, and a point-preserving diffeomorphism between the two structures.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace CompatibleAtlasesTest

private abbrev Plane := ℝ × ℝ

private def shearEquiv : Plane ≃ Plane where
  toFun p := (p.1 + 1, p.2 + p.1 ^ 2)
  invFun p := (p.1 - 1, p.2 - (p.1 - 1) ^ 2)
  left_inv p := by
    dsimp
    ext <;> ring
  right_inv p := by
    dsimp
    ext <;> ring

private def shearHomeomorph : Plane ≃ₜ Plane where
  toEquiv := shearEquiv
  continuous_toFun := by
    change Continuous (fun p : Plane => (p.1 + 1, p.2 + p.1 ^ 2))
    fun_prop
  continuous_invFun := by
    change Continuous (fun p : Plane => (p.1 - 1, p.2 - (p.1 - 1) ^ 2))
    fun_prop

private def shearChart : OpenPartialHomeomorph Plane Plane :=
  shearHomeomorph.toOpenPartialHomeomorph

@[instance_reducible]
private def identityAtlas : ChartedSpace Plane Plane := chartedSpaceSelf Plane

@[instance_reducible]
private def shearAtlas : ChartedSpace Plane Plane :=
  shearChart.singletonChartedSpace (by simp [shearChart])

@[instance_reducible]
private def identityWithShearAtlas : ChartedSpace Plane Plane where
  atlas := {OpenPartialHomeomorph.refl Plane, shearChart}
  chartAt _ := OpenPartialHomeomorph.refl Plane
  mem_chart_source _ := by simp
  chart_mem_atlas _ := by simp

private theorem shear_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : Plane => (p.1 + 1, p.2 + p.1 ^ 2)) := by
  exact (contDiff_fst.add contDiff_const).prodMk
    (contDiff_snd.add (contDiff_fst.pow 2))

private theorem shear_symm_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : Plane => (p.1 - 1, p.2 - (p.1 - 1) ^ 2)) := by
  exact (contDiff_fst.sub contDiff_const).prodMk
    (contDiff_snd.sub ((contDiff_fst.sub contDiff_const).pow 2))

private theorem mixed (n : ℕ∞ω) :
    ∀ e ∈ identityAtlas.atlas, ∀ f ∈ shearAtlas.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid n 𝓘(ℝ, Plane) := by
  intro e he f hf
  have heq : e = OpenPartialHomeomorph.refl Plane := by
    change e ∈ ({OpenPartialHomeomorph.refl Plane} : Set _) at he
    exact he
  have hfq : f = shearChart := by
    exact shearChart.singletonChartedSpace_mem_atlas_eq (by simp [shearChart]) f hf
  subst e
  subst f
  rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans]
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · change ContDiffOn ℝ n (𝓘(ℝ, Plane) ∘ shearChart ∘ 𝓘(ℝ, Plane).symm)
        (𝓘(ℝ, Plane).symm ⁻¹' shearChart.source ∩ Set.range 𝓘(ℝ, Plane))
    simpa [shearChart, shearHomeomorph, shearEquiv] using (shear_contDiff n).contDiffOn
  · change ContDiffOn ℝ n (𝓘(ℝ, Plane) ∘ shearChart.symm ∘ 𝓘(ℝ, Plane).symm)
        (𝓘(ℝ, Plane).symm ⁻¹' shearChart.target ∩ Set.range 𝓘(ℝ, Plane))
    simpa [shearChart, shearHomeomorph, shearEquiv] using (shear_symm_contDiff n).contDiffOn

example : identityAtlas.chartAt (0, 0) ≠ shearAtlas.chartAt (0, 0) := by
  have hid : identityAtlas.chartAt (0, 0) = OpenPartialHomeomorph.refl Plane := rfl
  have hshear : shearAtlas.chartAt (0, 0) = shearChart := rfl
  intro h
  rw [hid, hshear] at h
  have hpoint := congrArg (fun e : OpenPartialHomeomorph Plane Plane => e (0, 0)) h
  norm_num [shearChart, shearHomeomorph, shearEquiv] at hpoint

example : shearChart (1, 0) = (2, 1) := by
  norm_num [shearChart, shearHomeomorph, shearEquiv]

example : (Homeomorph.ulift : ULift Plane ≃ₜ Plane).toOpenPartialHomeomorph ≫ₕ
      shearChart ∈ (ChartedSpace.liftedChartedSpace shearAtlas).atlas := by
  apply (ChartedSpace.mem_liftedChartedSpace_atlas_iff _ _).2
  exact ⟨shearChart, rfl, rfl⟩

example : shearChart ∈ identityWithShearAtlas.atlas ∧
    ∀ x : Plane, identityWithShearAtlas.chartAt x ≠ shearChart := by
  constructor
  · change shearChart = OpenPartialHomeomorph.refl Plane ∨ shearChart = shearChart
    exact Or.inr rfl
  · intro x h
    change OpenPartialHomeomorph.refl Plane = shearChart at h
    have hpoint := congrArg (fun e : OpenPartialHomeomorph Plane Plane => e (0, 0)) h
    norm_num [shearChart, shearHomeomorph, shearEquiv] at hpoint

example : (Homeomorph.ulift : ULift Plane ≃ₜ Plane).toOpenPartialHomeomorph ≫ₕ
      shearChart ∈ (ChartedSpace.liftedChartedSpace identityWithShearAtlas).atlas := by
  apply (ChartedSpace.mem_liftedChartedSpace_atlas_iff _ _).2
  exact ⟨shearChart, Or.inr rfl, rfl⟩

example : (identityAtlas.chartAt (0, 0)) (0, 0) ≠
    ((ChartedSpace.liftedChartedSpace shearAtlas).chartAt
      (ULift.up (0, 0))) (ULift.up (0, 0)) := by
  have hid : identityAtlas.chartAt (0, 0) = OpenPartialHomeomorph.refl Plane := rfl
  rw [ChartedSpace.liftedChartedSpace_chartAt_apply]
  rw [hid]
  norm_num [shearAtlas, shearChart, shearHomeomorph, shearEquiv]

example : @HasGroupoid Plane _ Plane _ identityAtlas (contDiffGroupoid ∞ 𝓘(ℝ, Plane)) ∧
    @HasGroupoid Plane _ Plane _ shearAtlas (contDiffGroupoid ∞ 𝓘(ℝ, Plane)) :=
  ChartedSpace.hasGroupoid_of_compatible_atlases _ _ _ (mixed ∞)

example : @StructureGroupoid.maximalAtlas Plane Plane _ _ identityAtlas
      (contDiffGroupoid 2 𝓘(ℝ, Plane)) =
    @StructureGroupoid.maximalAtlas Plane Plane _ _ shearAtlas
      (contDiffGroupoid 2 𝓘(ℝ, Plane)) :=
  ChartedSpace.maximalAtlas_eq_of_compatible_atlases _ _ _ (mixed 2)

example : @IsManifold ℝ _ Plane _ _ Plane _ 𝓘(ℝ, Plane) 2 Plane _ identityAtlas ∧
    @IsManifold ℝ _ Plane _ _ Plane _ 𝓘(ℝ, Plane) 2 Plane _ shearAtlas :=
  ChartedSpace.isManifold_of_compatible_atlases _ _ _ _ (mixed 2)

example : @IsManifold ℝ _ Plane _ _ Plane _ 𝓘(ℝ, Plane) ∞ Plane _ identityAtlas ∧
    @IsManifold ℝ _ Plane _ _ Plane _ 𝓘(ℝ, Plane) ∞ Plane _ shearAtlas :=
  ChartedSpace.isManifold_of_compatible_atlases _ _ _ _ (mixed ∞)

example (p : Plane) :
    ChartedSpace.identityDiffeomorph 𝓘(ℝ, Plane) 2 identityAtlas shearAtlas (mixed 2) p =
      ULift.up p := by
  simp

example (p : ULift Plane) :
    ChartedSpace.identityDiffeomorph 𝓘(ℝ, Plane) ∞ identityAtlas shearAtlas
      (mixed ∞) p.down = p := by
  simp

example (p : ULift Plane) :
    (@Diffeomorph.symm ℝ _ Plane _ _ Plane _ _ Plane _ Plane _
      𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane _ identityAtlas (ULift Plane) _
      (ChartedSpace.liftedChartedSpace shearAtlas) 2
      (ChartedSpace.identityDiffeomorph 𝓘(ℝ, Plane) 2 identityAtlas shearAtlas
        (mixed 2))) p = p.down := by
  simp

private abbrev ZeroModel := EuclideanSpace ℝ (Fin 0)

private theorem zeroMixed (n : ℕ∞ω) :
    ∀ e ∈ (chartedSpaceSelf ZeroModel).atlas,
      ∀ f ∈ (chartedSpaceSelf ZeroModel).atlas,
        e.symm ≫ₕ f ∈ contDiffGroupoid n 𝓘(ℝ, ZeroModel) := by
  intro e he f hf
  rw [chartedSpaceSelf_atlas] at he hf
  subst e
  subst f
  rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans]
  exact (contDiffGroupoid n 𝓘(ℝ, ZeroModel)).id_mem

example : @IsManifold ℝ _ ZeroModel _ _ ZeroModel _ 𝓘(ℝ, ZeroModel) ∞
      ZeroModel _ (chartedSpaceSelf ZeroModel) :=
  (ChartedSpace.isManifold_of_compatible_atlases 𝓘(ℝ, ZeroModel) ∞
    (chartedSpaceSelf ZeroModel) (chartedSpaceSelf ZeroModel) (zeroMixed ∞)).1

private theorem emptyMixed (n : ℕ∞ω) :
    ∀ e ∈ (ChartedSpace.empty Plane Empty).atlas,
      ∀ f ∈ (ChartedSpace.empty Plane Empty).atlas,
        e.symm ≫ₕ f ∈ contDiffGroupoid n 𝓘(ℝ, Plane) := by
  intro e he
  change e ∈ (∅ : Set (OpenPartialHomeomorph Empty Plane)) at he
  exact False.elim he

example : @HasGroupoid Plane _ Empty _ (ChartedSpace.empty Plane Empty)
      (contDiffGroupoid 1 𝓘(ℝ, Plane)) :=
  (ChartedSpace.hasGroupoid_of_compatible_atlases _ _ _ (emptyMixed 1)).1

end CompatibleAtlasesTest
