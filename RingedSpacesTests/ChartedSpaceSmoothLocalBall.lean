/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Canonical smooth scalar functions on chart balls

A proper open real interval has a nonconstant section whose pullback through
the restricted-ambient smooth scalar locally ringed-space isomorphism evaluates
to two. The zero-dimensional model supports constant sections, while an empty
carrier requires no chosen point.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace ChartedSpaceSmoothLocalBallTest

open ChartedSpace

def interval : Opens ℝ := ⟨Set.Ioo (-1) 1, isOpen_Ioo⟩

private def origin : interval := ⟨0, by norm_num [interval]⟩

example : (origin : ℝ) ∈ interval ∧ (2 : ℝ) ∉ interval :=
  ⟨origin.2, by norm_num [interval]⟩

private def chartData : ChartLocalBall (𝕜 := ℝ) (E := ℝ) (∞ : ℕ∞ω) origin :=
  chartLocalBall ∞ origin

example : origin ∈ chartData.neighborhood ∧ 0 < chartData.radius ∧
    (chartAt ℝ origin) origin ∈ chartData.ball :=
  ⟨chartData.mem_neighborhood, chartData.radius_pos, chartData.center_mem_ball⟩

private def coordinate :
    (smoothSheafCommRing 𝓘(ℝ) 𝓘(ℝ) chartData.ball ℝ).presheaf.obj
      (op (⊤ : Opens chartData.ball)) :=
  ⟨fun point => ((point : chartData.ball) : ℝ) + 2,
    (contMDiff_subtype_val.comp contMDiff_subtype_val).add contMDiff_const⟩

private def point : chartData.neighborhood := ⟨origin, chartData.mem_neighborhood⟩

private theorem coordinate_at_point :
    coordinate ⟨chartData.coord point, by simp⟩ = 2 := by
  change ((chartData.coord point : chartData.ball) : ℝ) + 2 = 2
  rw [chartData.coord_apply]
  change (chartAt ℝ (origin : ℝ)) (origin : ℝ) + 2 = 2
  simp [chartAt_self_eq, origin]

private def offCenter : chartData.ball :=
  ⟨(chartAt ℝ origin) origin + chartData.radius / 2, by
    rw [chartData.mem_ball, Real.dist_eq]
    have hr : 0 < chartData.radius / 2 := by linarith [chartData.radius_pos]
    simpa [abs_of_pos hr] using (show chartData.radius / 2 < chartData.radius by
      linarith [chartData.radius_pos])⟩

example : ∃ first second : (⊤ : Opens chartData.ball),
    coordinate first ≠ coordinate second := by
  refine ⟨⟨chartData.center, by simp⟩, ⟨offCenter, by simp⟩, ?_⟩
  change (chartAt ℝ origin) origin + 2 ≠
    ((chartAt ℝ origin) origin + chartData.radius / 2) + 2
  linarith [chartData.radius_pos]

example : smoothSheafCommRing.eval 𝓘(ℝ) 𝓘(ℝ) chartData.neighborhood ℝ point
    (((restrictLocallyRingedSpaceIso (IM := 𝓘(ℝ)) (M := interval)
      chartData.neighborhood).inv ≫
      chartData.smoothIso.hom).stalkMap point
      ((smoothSheafCommRing 𝓘(ℝ) 𝓘(ℝ) chartData.ball ℝ).presheaf.germ ⊤
        (((restrictLocallyRingedSpaceIso (IM := 𝓘(ℝ)) (M := interval)
          chartData.neighborhood).inv ≫ chartData.smoothIso.hom).base point)
        (by simp) coordinate)) = 2 := by
  exact (chartData.smoothIso_hom_germ_eval ⊤ point (by simp) coordinate).trans
    coordinate_at_point

example : smoothSheafCommRing.eval 𝓘(ℝ) 𝓘(ℝ) chartData.neighborhood ℝ point
    ((smoothSheafCommRing 𝓘(ℝ) 𝓘(ℝ) chartData.neighborhood ℝ).presheaf.germ
      ((Opens.map ((restrictLocallyRingedSpaceIso (IM := 𝓘(ℝ)) (M := interval)
        chartData.neighborhood).inv ≫ chartData.smoothIso.hom).base).obj ⊤)
      point (by simp)
      (((restrictLocallyRingedSpaceIso (IM := 𝓘(ℝ)) (M := interval)
        chartData.neighborhood).inv ≫
        chartData.smoothIso.hom).c.app (op (⊤ : Opens chartData.ball)) coordinate)) = 2 := by
  exact (chartData.smoothIso_hom_section_germ_eval ⊤ point (by simp) coordinate).trans
    coordinate_at_point

private def dimensionZeroData (modelPoint : EuclideanSpace ℝ (Fin 0)) :
    ChartLocalBall (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 0))
      (∞ : ℕ∞ω) modelPoint :=
  chartLocalBall ∞ modelPoint

private def constantSection (modelPoint : EuclideanSpace ℝ (Fin 0)) :
    (smoothSheafCommRing 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 𝓘(ℝ)
      (dimensionZeroData modelPoint).ball ℝ).presheaf.obj
      (op (⊤ : Opens (dimensionZeroData modelPoint).ball)) :=
  ⟨fun _ => (4 : ℝ), contMDiff_const⟩

example (modelPoint : EuclideanSpace ℝ (Fin 0)) :
    let b := dimensionZeroData modelPoint
    0 < b.radius ∧
      smoothSheafCommRing.eval 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 𝓘(ℝ)
        b.neighborhood ℝ ⟨modelPoint, b.mem_neighborhood⟩
        ((smoothSheafCommRing 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 𝓘(ℝ)
          b.neighborhood ℝ).presheaf.germ
          ((Opens.map ((restrictLocallyRingedSpaceIso
            (IM := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
            (M := EuclideanSpace ℝ (Fin 0)) b.neighborhood).inv ≫
            b.smoothIso.hom).base).obj ⊤)
          ⟨modelPoint, b.mem_neighborhood⟩ (by simp)
          (((restrictLocallyRingedSpaceIso
            (IM := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
            (M := EuclideanSpace ℝ (Fin 0)) b.neighborhood).inv ≫
            b.smoothIso.hom).c.app
            (op (⊤ : Opens b.ball)) (constantSection modelPoint))) = 4 := by
  dsimp only
  constructor
  · exact (dimensionZeroData modelPoint).radius_pos
  · exact ((dimensionZeroData modelPoint).smoothIso_hom_section_germ_eval ⊤
      ⟨modelPoint, (dimensionZeroData modelPoint).mem_neighborhood⟩ (by simp)
      (constantSection modelPoint)).trans (by simp [constantSection])

private instance : ChartedSpace ℝ Empty := ChartedSpace.empty ℝ Empty

example : ∀ x : Empty, ChartLocalBall (𝕜 := ℝ) (E := ℝ) (∞ : ℕ∞ω) x :=
  fun x => isEmptyElim x

end ChartedSpaceSmoothLocalBallTest
