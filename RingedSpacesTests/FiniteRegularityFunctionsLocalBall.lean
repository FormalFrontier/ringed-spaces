/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Local-ball scalar-function examples

An open real interval supplies a proper, inhabited manifold. The coordinate map
on its local ball acts nontrivially on a scalar section and its germ. The empty
manifold has no point at which to demand a ball; zero-dimensional and zero-order
model spaces still admit balls around each of their points.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace FiniteRegularityFunctionsLocalBallTest

open FiniteRegularityFunctions

def interval : Opens ℝ := ⟨Set.Ioo (-1) 1, isOpen_Ioo⟩

private def origin : interval := ⟨0, by norm_num [interval]⟩

example : (origin : ℝ) ∈ interval ∧ (2 : ℝ) ∉ interval := by
  exact ⟨origin.2, by norm_num [interval]⟩

private def chartData : LocalBall (𝕜 := ℝ) (E := ℝ) 1 origin := localBall 1 origin

example : origin ∈ chartData.neighborhood ∧ 0 < chartData.radius ∧
    (chartAt ℝ origin) origin ∈ chartData.ball :=
  ⟨chartData.mem_neighborhood, chartData.radius_pos, chartData.center_mem_ball⟩

private def coordinate :
    (sheaf 𝓘(ℝ) chartData.ball 1).presheaf.obj (op (⊤ : Opens chartData.ball)) :=
  ofFunction (IM := 𝓘(ℝ)) (M := chartData.ball) 1 ⊤
    (fun point => (point : ℝ) + 2)
    ((contMDiff_subtype_val.comp contMDiff_subtype_val).add contMDiff_const)

private def point : chartData.neighborhood := ⟨origin, chartData.mem_neighborhood⟩

private theorem coordinate_at_point :
    coordinate ⟨chartData.coord point, by simp⟩ = 2 := by
  change ((chartData.coord point : chartData.ball) : ℝ) + 2 = 2
  rw [chartData.coord_apply]
  change (chartAt ℝ (origin : ℝ)) (origin : ℝ) + 2 = 2
  simp [chartAt_self_eq, origin]

example : eval 𝓘(ℝ) chartData.neighborhood 1 point
    ((restrictLocallyRingedSpaceIso 𝓘(ℝ) interval 1 chartData.neighborhood).inv.stalkMap
      point
      (chartData.iso.hom.stalkMap
        ((restrictLocallyRingedSpaceIso 𝓘(ℝ) interval 1 chartData.neighborhood).inv.base
          point)
        ((sheaf 𝓘(ℝ) chartData.ball 1).presheaf.germ ⊤
          (chartData.coord point) (by simp) coordinate))) = 2 := by
  rw [chartData.iso_hom_germ_eval]
  exact coordinate_at_point

example : eval 𝓘(ℝ) chartData.neighborhood 1 point
    ((sheaf 𝓘(ℝ) chartData.neighborhood 1).presheaf.germ
      ((Opens.map ((restrictLocallyRingedSpaceIso 𝓘(ℝ) interval 1
        chartData.neighborhood).inv ≫ chartData.iso.hom).base).obj ⊤)
      point (by simp)
      (((restrictLocallyRingedSpaceIso 𝓘(ℝ) interval 1 chartData.neighborhood).inv ≫
        chartData.iso.hom).c.app (op (⊤ : Opens chartData.ball)) coordinate)) = 2 := by
  exact (chartData.iso_hom_section_germ_eval ⊤ point (by simp) coordinate).trans
    coordinate_at_point

private def orderZeroData (modelPoint : EuclideanSpace ℝ (Fin 2)) :
    LocalBall (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 2)) 0 modelPoint :=
  localBall 0 modelPoint

private def dimensionZeroData (modelPoint : EuclideanSpace ℝ (Fin 0)) :
    LocalBall (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 0)) 1 modelPoint :=
  localBall 1 modelPoint

example (modelPoint : EuclideanSpace ℝ (Fin 2)) :
    let b := orderZeroData modelPoint
    0 < b.radius ∧
      eval 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) b.neighborhood 0
        (⟨modelPoint, b.mem_neighborhood⟩ : b.neighborhood)
        ((sheaf 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) b.neighborhood 0).presheaf.germ
          ((Opens.map ((restrictLocallyRingedSpaceIso 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (EuclideanSpace ℝ (Fin 2)) 0 b.neighborhood).inv ≫ b.iso.hom).base).obj ⊤)
          ⟨modelPoint, b.mem_neighborhood⟩ (by simp)
          (((restrictLocallyRingedSpaceIso 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (EuclideanSpace ℝ (Fin 2)) 0 b.neighborhood).inv ≫ b.iso.hom).c.app
            (op (⊤ : Opens b.ball))
            (ofFunction (IM := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
              (M := b.ball) 0 ⊤ (fun _ => (3 : ℝ)) contMDiff_const))) = 3 := by
  dsimp only
  constructor
  · exact (orderZeroData modelPoint).radius_pos
  · exact ((orderZeroData modelPoint).iso_hom_section_germ_eval ⊤
      ⟨modelPoint, (orderZeroData modelPoint).mem_neighborhood⟩ (by simp)
      (ofFunction (IM := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
        (M := (orderZeroData modelPoint).ball) 0 ⊤
        (fun _ => (3 : ℝ)) contMDiff_const)).trans (by simp)

example (modelPoint : EuclideanSpace ℝ (Fin 0)) :
    let b := dimensionZeroData modelPoint
    eval 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) b.neighborhood 1
      (⟨modelPoint, b.mem_neighborhood⟩ : b.neighborhood)
      ((restrictLocallyRingedSpaceIso 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
        (EuclideanSpace ℝ (Fin 0)) 1 b.neighborhood).inv.stalkMap
          ⟨modelPoint, b.mem_neighborhood⟩
        (b.iso.hom.stalkMap
          ((restrictLocallyRingedSpaceIso 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
            (EuclideanSpace ℝ (Fin 0)) 1 b.neighborhood).inv.base
            ⟨modelPoint, b.mem_neighborhood⟩)
          ((sheaf 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) b.ball 1).presheaf.germ ⊤
            (b.coord ⟨modelPoint, b.mem_neighborhood⟩) (by simp)
            (ofFunction (IM := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (M := b.ball) 1 ⊤
              (fun _ => (4 : ℝ)) contMDiff_const)))) = 4 := by
  dsimp only
  rw [(dimensionZeroData modelPoint).iso_hom_germ_eval]
  simp

private instance : ChartedSpace ℝ Empty := ChartedSpace.empty ℝ Empty

example : ∀ point : Empty, LocalBall (𝕜 := ℝ) (E := ℝ) 1 point :=
  fun point => isEmptyElim point

end FiniteRegularityFunctionsLocalBallTest
