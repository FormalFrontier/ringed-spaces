/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.ChartedSpace.CompatibleAtlasSheaf
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Two genuinely different compatible charts

The preferred charts on `ℝ × ℝ` are the identity and a global triangular polynomial shear.
The groupoid hypothesis is verified from the polynomial maps. The comparison theorems give
regularity, equal maximal atlases, and a point-preserving diffeomorphism between the two structures.
Further examples compare scalar sections on proper nested opens and evaluate germs in both
directions; a complex translation atlas and empty and zero-dimensional carriers test the scope.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold
open CategoryTheory TopologicalSpace Opposite

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

private def positiveOpen : Opens Plane :=
  ⟨{point | 0 < point.1}, isOpen_Ioi.preimage continuous_fst⟩

private def smallerOpen : Opens Plane :=
  ⟨{point | 1 < point.1}, isOpen_Ioi.preimage continuous_fst⟩

private theorem smaller_le_positive : smallerOpen ≤ positiveOpen := by
  intro point hpoint
  change 1 < point.1 at hpoint
  change 0 < point.1
  exact lt_trans zero_lt_one hpoint

private theorem one_mem_positive : (1, 0) ∈ positiveOpen := by
  change (0 : ℝ) < 1
  norm_num

private theorem smaller_lt_positive : smallerOpen < positiveOpen := by
  refine lt_of_le_of_ne smaller_le_positive ?_
  intro heq
  have hpoint : (1, 0) ∈ smallerOpen := heq.symm ▸ one_mem_positive
  change (1 : ℝ) < 1 at hpoint
  exact (lt_irrefl (1 : ℝ)) hpoint

private theorem two_mem_positive : (2, 0) ∈ positiveOpen := by
  change (0 : ℝ) < 2
  norm_num

private theorem two_mem_smaller : (2, 0) ∈ smallerOpen := by
  change (1 : ℝ) < 2
  norm_num

private def coordinateSection :
    (ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane) identityAtlas).presheaf.obj
      (op positiveOpen) := by
  letI : ChartedSpace Plane Plane := identityAtlas
  have hfst : ContDiff ℝ ∞ (fun point : Plane => point.1) := contDiff_fst
  exact ⟨fun point : positiveOpen => point.1.1,
    hfst.contMDiff.comp contMDiff_subtype_val⟩

example : positiveOpen ≠ (⊤ : Opens Plane) ∧ smallerOpen ≠ (⊤ : Opens Plane) := by
  constructor <;> intro h
  · have hpoint : (0, 0) ∈ positiveOpen := h.symm ▸ trivial
    change (0 : ℝ) < 0 at hpoint
    exact (lt_irrefl (0 : ℝ)) hpoint
  · have hpoint : (0, 0) ∈ smallerOpen := h.symm ▸ trivial
    change (1 : ℝ) < 0 at hpoint
    norm_num at hpoint

private theorem coordinateSection_not_constant :
    coordinateSection.1 ⟨(1, 0), one_mem_positive⟩ ≠
    coordinateSection.1 ⟨(2, 0), two_mem_positive⟩ := by
  norm_num [coordinateSection]

private theorem atlasIso_base_preserving (point : Plane) :
    (ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
      identityAtlas shearAtlas (mixed ∞)).hom.base point = point ∧
    (ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
      identityAtlas shearAtlas (mixed ∞)).inv.base point = point := by
  constructor <;> rfl

private theorem inverseSection_value :
    (((ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
      identityAtlas shearAtlas (mixed ∞)).inv.c.app (op positiveOpen))
      coordinateSection).1 ⟨(2, 0), by change (2, 0) ∈ positiveOpen; exact two_mem_positive⟩ =
        2 := by
  rfl

private theorem inverseEquivSection_one_value :
    ((ChartedSpace.compatibleAtlasSectionRingEquiv 𝓘(ℝ, Plane)
      identityAtlas shearAtlas (mixed ∞) positiveOpen).symm
      coordinateSection).1 ⟨(1, 0), one_mem_positive⟩ = 1 := by
  rw [ChartedSpace.compatibleAtlasSectionRingEquiv_symm_apply]
  rfl

private theorem inverseEquivSection_two_value :
    ((ChartedSpace.compatibleAtlasSectionRingEquiv 𝓘(ℝ, Plane)
      identityAtlas shearAtlas (mixed ∞) positiveOpen).symm
      coordinateSection).1 ⟨(2, 0), two_mem_positive⟩ = 2 := by
  rw [ChartedSpace.compatibleAtlasSectionRingEquiv_symm_apply]
  rfl

private theorem inverseEquivSection_not_constant :
    ((ChartedSpace.compatibleAtlasSectionRingEquiv 𝓘(ℝ, Plane)
      identityAtlas shearAtlas (mixed ∞) positiveOpen).symm
      coordinateSection).1 ⟨(1, 0), one_mem_positive⟩ ≠
    ((ChartedSpace.compatibleAtlasSectionRingEquiv 𝓘(ℝ, Plane)
      identityAtlas shearAtlas (mixed ∞) positiveOpen).symm
      coordinateSection).1 ⟨(2, 0), two_mem_positive⟩ := by
  rw [inverseEquivSection_one_value, inverseEquivSection_two_value]
  norm_num

private theorem sectionRoundtrip_value :
    (((ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
      identityAtlas shearAtlas (mixed ∞)).hom.c.app (op positiveOpen))
      (((ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
        identityAtlas shearAtlas (mixed ∞)).inv.c.app (op positiveOpen))
        coordinateSection)).1 ⟨(2, 0), by
          change (2, 0) ∈ positiveOpen
          exact two_mem_positive⟩ = 2 := by
  rfl

private theorem inverseSection_restrict_value :
    ((ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane) shearAtlas).presheaf.map
      (homOfLE smaller_le_positive).op
      (((ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
        identityAtlas shearAtlas (mixed ∞)).inv.c.app (op positiveOpen))
        coordinateSection)).1 ⟨(2, 0), two_mem_smaller⟩ = 2 := by
  rfl

private theorem inverseEquivSection_restrict_value :
    ((ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane) shearAtlas).presheaf.map
      (homOfLE smaller_le_positive).op
      ((ChartedSpace.compatibleAtlasSectionRingEquiv 𝓘(ℝ, Plane)
        identityAtlas shearAtlas (mixed ∞) positiveOpen).symm
        coordinateSection)).1 ⟨(2, 0), two_mem_smaller⟩ = 2 := by
  have hrestrict := ChartedSpace.compatibleAtlasSectionRingEquiv_symm_restrict
    𝓘(ℝ, Plane) identityAtlas shearAtlas (mixed ∞) smaller_le_positive coordinateSection
  have hvalue := ChartedSpace.compatibleAtlasSectionRingEquiv_symm_apply
    𝓘(ℝ, Plane) identityAtlas shearAtlas (mixed ∞) smallerOpen
    ((ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane) identityAtlas).presheaf.map
      (homOfLE smaller_le_positive).op coordinateSection) ⟨(2, 0), two_mem_smaller⟩
  exact ((congrArg (fun (restrictedSection :
      (ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane) shearAtlas).presheaf.obj
        (op smallerOpen)) => restrictedSection.1 ⟨(2, 0), two_mem_smaller⟩)
      hrestrict).trans hvalue).trans (by rfl)

private theorem inverseGerm_eval :
    ChartedSpace.smoothScalarStalkEval 𝓘(ℝ, Plane) shearAtlas (2, 0)
      ((ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
        identityAtlas shearAtlas (mixed ∞)).inv.stalkMap (2, 0)
        ((ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane) identityAtlas).presheaf.germ
          positiveOpen (2, 0) two_mem_positive coordinateSection)) = 2 := by
  rw [ChartedSpace.compatibleAtlasLocallyRingedSpaceIso_inv_germ_eval]
  rfl

private theorem forwardGerm_eval :
    ChartedSpace.smoothScalarStalkEval 𝓘(ℝ, Plane) identityAtlas (2, 0)
      ((ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
        identityAtlas shearAtlas (mixed ∞)).hom.stalkMap (2, 0)
        ((ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane) shearAtlas).presheaf.germ
          positiveOpen (2, 0) two_mem_positive
          (((ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
            identityAtlas shearAtlas (mixed ∞)).inv.c.app (op positiveOpen))
            coordinateSection))) = 2 := by
  have hvalue :
      (((ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
        identityAtlas shearAtlas (mixed ∞)).inv.c.app (op positiveOpen))
        coordinateSection).1 ⟨(2, 0), two_mem_positive⟩ = 2 := rfl
  exact (ChartedSpace.compatibleAtlasLocallyRingedSpaceIso_hom_germ_eval
    𝓘(ℝ, Plane) identityAtlas shearAtlas (mixed ∞) positiveOpen
    (2, 0) two_mem_positive _).trans hvalue

private theorem mixedWithExtra :
    ∀ e ∈ identityAtlas.atlas, ∀ f ∈ identityWithShearAtlas.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ 𝓘(ℝ, Plane) := by
  intro e he f hf
  change f = OpenPartialHomeomorph.refl Plane ∨ f = shearChart at hf
  rcases hf with rfl | rfl
  · have heq : e = OpenPartialHomeomorph.refl Plane := by
      change e ∈ ({OpenPartialHomeomorph.refl Plane} : Set _) at he
      exact he
    subst e
    rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans]
    exact (contDiffGroupoid ∞ 𝓘(ℝ, Plane)).id_mem
  · exact mixed ∞ e he shearChart rfl

private theorem extraChart_atlasIso_base :
    (Homeomorph.ulift : ULift Plane ≃ₜ Plane).toOpenPartialHomeomorph ≫ₕ
        shearChart ∈ (ChartedSpace.liftedChartedSpace identityWithShearAtlas).atlas ∧
    (ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
      identityAtlas identityWithShearAtlas mixedWithExtra).hom.base (2, 0) = (2, 0) := by
  constructor
  · exact (ChartedSpace.mem_liftedChartedSpace_atlas_iff _ _).2
      ⟨shearChart, Or.inr rfl, rfl⟩
  · rfl

private def zeroModel_atlasIso : ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, ZeroModel)
      (chartedSpaceSelf ZeroModel) ≅
    ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, ZeroModel)
      (chartedSpaceSelf ZeroModel) :=
  ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, ZeroModel)
    (chartedSpaceSelf ZeroModel) (chartedSpaceSelf ZeroModel) (zeroMixed ∞)

private def empty_atlasIso : ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane)
      (ChartedSpace.empty Plane Empty) ≅
    ChartedSpace.smoothScalarLocallyRingedSpace 𝓘(ℝ, Plane)
      (ChartedSpace.empty Plane Empty) :=
  ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℝ, Plane)
    (ChartedSpace.empty Plane Empty) (ChartedSpace.empty Plane Empty) (emptyMixed ∞)

private def translatedComplexChart : OpenPartialHomeomorph ℂ ℂ :=
  (Homeomorph.addLeft (1 : ℂ)).toOpenPartialHomeomorph

@[instance_reducible]
private def translatedComplexAtlas : ChartedSpace ℂ ℂ :=
  translatedComplexChart.singletonChartedSpace (by simp [translatedComplexChart])

private theorem complexMixed :
    ∀ e ∈ (chartedSpaceSelf ℂ).atlas, ∀ f ∈ translatedComplexAtlas.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ 𝓘(ℂ) := by
  intro e he f hf
  have heq : e = OpenPartialHomeomorph.refl ℂ := by
    change e ∈ ({OpenPartialHomeomorph.refl ℂ} : Set _) at he
    exact he
  have hfq : f = translatedComplexChart := by
    exact translatedComplexChart.singletonChartedSpace_mem_atlas_eq
      (by simp [translatedComplexChart]) f hf
  subst e
  subst f
  rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans]
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · change ContDiffOn ℂ ∞ (𝓘(ℂ) ∘ translatedComplexChart ∘ 𝓘(ℂ).symm)
        (𝓘(ℂ).symm ⁻¹' translatedComplexChart.source ∩ Set.range 𝓘(ℂ))
    simpa [translatedComplexChart, Homeomorph.addLeft] using
      ((contDiff_const : ContDiff ℂ ∞ (fun _ : ℂ => (1 : ℂ))).add contDiff_id).contDiffOn
  · change ContDiffOn ℂ ∞ (𝓘(ℂ) ∘ translatedComplexChart.symm ∘ 𝓘(ℂ).symm)
        (𝓘(ℂ).symm ⁻¹' translatedComplexChart.target ∩ Set.range 𝓘(ℂ))
    simpa [translatedComplexChart, Homeomorph.addLeft] using
      ((contDiff_const : ContDiff ℂ ∞ (fun _ : ℂ => (-1 : ℂ))).add contDiff_id).contDiffOn

private theorem complexAtlasIso_base (point : ℂ) :
    (ChartedSpace.compatibleAtlasLocallyRingedSpaceIso 𝓘(ℂ)
      (chartedSpaceSelf ℂ) translatedComplexAtlas complexMixed).hom.base point = point := by
  rfl

private theorem complexAtlasScalar (scalar : ℂ) :
    ChartedSpace.compatibleAtlasSectionRingEquiv 𝓘(ℂ)
      (chartedSpaceSelf ℂ) translatedComplexAtlas complexMixed ⊤
      (ChartedSpace.smoothScalarConstant 𝓘(ℂ) translatedComplexAtlas ⊤ scalar) =
        ChartedSpace.smoothScalarConstant 𝓘(ℂ) (chartedSpaceSelf ℂ) ⊤ scalar := by
  exact ChartedSpace.compatibleAtlasSectionRingEquiv_constant 𝓘(ℂ)
    (chartedSpaceSelf ℂ) translatedComplexAtlas complexMixed ⊤ scalar

private theorem complexAtlasInverseScalar (scalar : ℂ) :
    (ChartedSpace.compatibleAtlasSectionRingEquiv 𝓘(ℂ)
      (chartedSpaceSelf ℂ) translatedComplexAtlas complexMixed ⊤).symm
      (ChartedSpace.smoothScalarConstant 𝓘(ℂ) (chartedSpaceSelf ℂ) ⊤ scalar) =
        ChartedSpace.smoothScalarConstant 𝓘(ℂ) translatedComplexAtlas ⊤ scalar := by
  exact ChartedSpace.compatibleAtlasSectionRingEquiv_symm_constant 𝓘(ℂ)
    (chartedSpaceSelf ℂ) translatedComplexAtlas complexMixed ⊤ scalar

end CompatibleAtlasesTest
