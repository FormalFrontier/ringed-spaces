/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces

/-!
# Holomorphic scalar sections on a proper complex disc

A nonconstant holomorphic function on the entire chart ball gives a section whose
value is computed through the complete restricted-ambient chart morphism.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace HolomorphicSectionsTest

open ChartedSpace

def disc : Opens ℂ := ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩

private def origin : disc := ⟨0, by simp [disc]⟩

example : (2 : ℂ) ∉ disc := by
  simp [disc, Metric.mem_ball, dist_eq_norm]

example : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
    (fun _ : (⊥ : Opens ℂ) ↦ (0 : ℂ)) :=
  mdifferentiable_const

example (D : Opens ℂ) (value : ℂ) :
    ∃ representativeSection :
        (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj (op (⊤ : Opens D)),
      ∀ point : (⊤ : Opens D), representativeSection point = value := by
  exact ⟨ComplexLine.ofHolomorphic D ⊤ (fun _ ↦ value) mdifferentiable_const,
    fun _ ↦ rfl⟩

private def chartData : ChartLocalBall (𝕜 := ℂ) (E := ℂ) (∞ : ℕ∞ω) origin :=
  chartLocalBall ∞ origin

private def representative (point : (⊤ : Opens chartData.ball)) : ℂ :=
  ((point : chartData.ball) : ℂ) + 2

private theorem representative_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) representative := by
  have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun point : (⊤ : Opens chartData.ball) ↦ ((point : chartData.ball) : ℂ)) :=
    ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num)).comp
      ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))
  exact hval.add mdifferentiable_const

private theorem representative_smooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ representative :=
  (ComplexLine.smooth_iff_holomorphic chartData.ball ⊤ representative).2
    representative_holomorphic

example : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) representative := by
  have hsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ representative :=
    (contMDiff_subtype_val.comp contMDiff_subtype_val).add contMDiff_const
  exact (ComplexLine.smooth_iff_holomorphic chartData.ball ⊤ representative).1 hsmooth

private def openRepresentative (point : disc) : ℂ := (point : ℂ) + 2

private theorem openRepresentative_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) openRepresentative := by
  have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : disc → ℂ) :=
    (contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num)
  exact hval.add mdifferentiable_const

private theorem openRepresentative_smooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ openRepresentative :=
  (ComplexLine.smooth_iff_holomorphic_open disc openRepresentative).2
    openRepresentative_holomorphic

example : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) openRepresentative := by
  have hsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ openRepresentative :=
    contMDiff_subtype_val.add contMDiff_const
  exact (ComplexLine.smooth_iff_holomorphic_open disc openRepresentative).1 hsmooth

private def translate (point : disc) : (⊤ : Opens ℂ) :=
  ⟨openRepresentative point, trivial⟩

private theorem translate_holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) translate := by
  have hsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ translate :=
    (ContMDiff.subtypeVal_comp_iff (⊤ : Opens ℂ) translate).mp openRepresentative_smooth
  exact hsmooth.mdifferentiable (by norm_num)

private def imageHalfDisc : Opens (⊤ : Opens ℂ) :=
  ⟨Metric.ball (⟨2, trivial⟩ : (⊤ : Opens ℂ)) (1 / 2), Metric.isOpen_ball⟩

private def imageCoordinate (point : imageHalfDisc) : ℂ := ((point : (⊤ : Opens ℂ)) : ℂ)

private theorem imageCoordinate_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) imageCoordinate :=
  ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num)).comp
    ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))

example : (translate origin : ℂ) ≠ (origin : ℂ) := by
  norm_num [translate, openRepresentative, origin]

private theorem origin_mem_preimage : origin ∈
    (Opens.map (TopCat.ofHom ⟨translate,
      (ComplexLine.holomorphic_contMDiff translate translate_holomorphic).continuous⟩)).obj
        imageHalfDisc := by
  change translate origin ∈ imageHalfDisc
  norm_num [translate, openRepresentative, origin, imageHalfDisc, Metric.mem_ball, dist_eq_norm]

private def outsidePreimage : disc :=
  ⟨(1 / 2 : ℂ), by norm_num [disc, Metric.mem_ball, dist_eq_norm]⟩

example : outsidePreimage ∉
    (Opens.map (TopCat.ofHom ⟨translate,
      (ComplexLine.holomorphic_contMDiff translate translate_holomorphic).continuous⟩)).obj
        imageHalfDisc := by
  change translate outsidePreimage ∉ imageHalfDisc
  norm_num [translate, openRepresentative, outsidePreimage, imageHalfDisc,
    Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]

example : ((ComplexLine.holomorphicSheafHom translate translate_holomorphic).hom.app
      (op imageHalfDisc)
      (ComplexLine.ofHolomorphic (⊤ : Opens ℂ) imageHalfDisc imageCoordinate
        imageCoordinate_holomorphic) :
      (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) disc ℂ).presheaf.obj
        (op ((Opens.map (TopCat.ofHom ⟨translate,
          (ComplexLine.holomorphic_contMDiff translate translate_holomorphic).continuous⟩)).obj
            imageHalfDisc))).1 ⟨origin, origin_mem_preimage⟩ = 2 := by
  rw [ComplexLine.holomorphicSheafHom_app_apply]
  norm_num [imageCoordinate, translate, openRepresentative, origin]

example : ((ComplexLine.holomorphicLocallyRingedSpaceMap translate translate_holomorphic).c.app
      (op imageHalfDisc)
      (ComplexLine.ofHolomorphic (⊤ : Opens ℂ) imageHalfDisc imageCoordinate
        imageCoordinate_holomorphic)) =
    ComplexLine.ofHolomorphic disc
      ((Opens.map (TopCat.ofHom ⟨translate,
        (ComplexLine.holomorphic_contMDiff translate translate_holomorphic).continuous⟩)).obj
        imageHalfDisc)
      (fun point ↦ imageCoordinate ⟨translate point.1, point.2⟩)
      (ComplexLine.holomorphic_precomp translate translate_holomorphic imageHalfDisc
        imageCoordinate imageCoordinate_holomorphic) := by
  exact ComplexLine.holomorphicLocallyRingedSpaceMap_c_app_ofHolomorphic
    translate translate_holomorphic imageHalfDisc imageCoordinate imageCoordinate_holomorphic

private def coordinate :
    (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) chartData.ball ℂ).presheaf.obj
      (op (⊤ : Opens chartData.ball)) :=
  ComplexLine.ofHolomorphic chartData.ball ⊤ representative representative_holomorphic

private def point : chartData.neighborhood := ⟨origin, chartData.mem_neighborhood⟩

private theorem coordinate_at_point : coordinate ⟨chartData.coord point, by simp⟩ = 2 := by
  change ((chartData.coord point : chartData.ball) : ℂ) + 2 = 2
  rw [chartData.coord_apply]
  change (chartAt ℂ (origin : ℂ)) (origin : ℂ) + 2 = 2
  simp [chartAt_self_eq, origin]

private def offCenter : chartData.ball :=
  ⟨(chartAt ℂ origin) origin + (chartData.radius / 2 : ℝ), by
    rw [chartData.mem_ball]
    have hr : 0 < chartData.radius / 2 := half_pos chartData.radius_pos
    have hlt : chartData.radius / 2 < chartData.radius := half_lt_self chartData.radius_pos
    calc
      dist ((chartAt ℂ origin) origin + (chartData.radius / 2 : ℝ))
          ((chartAt ℂ origin) origin) = ‖((chartData.radius / 2 : ℝ) : ℂ)‖ := by
            simp [dist_eq_norm]
      _ = chartData.radius / 2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      _ < chartData.radius := hlt⟩

example : ∃ first second : (⊤ : Opens chartData.ball),
    coordinate first ≠ coordinate second := by
  refine ⟨⟨chartData.center, by simp⟩, ⟨offCenter, by simp⟩, ?_⟩
  change (chartAt ℂ origin) origin + 2 ≠
    ((chartAt ℂ origin) origin + (chartData.radius / 2 : ℝ)) + 2
  intro heq
  have hz : ((chartData.radius / 2 : ℝ) : ℂ) = 0 := by
    have hbase := add_right_cancel heq.symm
    apply add_left_cancel (a := (chartAt ℂ origin) origin)
    simpa using hbase
  exact (ne_of_gt (half_pos chartData.radius_pos)) (Complex.ofReal_eq_zero.mp hz)

example : smoothSheafCommRing.eval 𝓘(ℂ) 𝓘(ℂ) chartData.neighborhood ℂ point
    ((smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) chartData.neighborhood ℂ).presheaf.germ
      ((Opens.map ((restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ)) (M := disc)
        chartData.neighborhood).inv ≫ chartData.smoothIso.hom).base).obj ⊤)
      point (by simp)
      (((restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ)) (M := disc)
        chartData.neighborhood).inv ≫
        chartData.smoothIso.hom).c.app (op (⊤ : Opens chartData.ball)) coordinate)) = 2 := by
  exact (chartData.smoothIso_hom_section_germ_eval ⊤ point (by simp) coordinate).trans
    coordinate_at_point

end HolomorphicSectionsTest
