/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.FiniteRegularityFunctions.OpenImmersion
public import RingedSpaces.ChartedSpace.LocalBall

/-!
# Finite-regularity scalar functions in local ball coordinates

On a manifold without boundary, a chart restricts near each point to a diffeomorphism
onto a positive-radius open ball in the normed model space. The resulting isomorphism
of finite-order scalar-function locally ringed spaces is built from the usual map on
functions and the comparison between an open subtype and a restricted space.

The model-with-corners structure is the self model. A chart at a boundary point for
a general model with corners need not contain any ambient open ball.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

universe u

namespace FiniteRegularityFunctions

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- The genuine open ball centered at the coordinate of a point in its chosen chart. -/
def chartBall (x : M) (radius : ℝ) : Opens E :=
  ChartedSpace.chartBall x radius

@[simp] theorem mem_chartBall (x : M) (radius : ℝ) (y : E) :
    y ∈ chartBall (E := E) x radius ↔ dist y ((chartAt E x) x) < radius :=
  Metric.mem_ball

/-- Coordinate data on an open neighborhood of a point, with a full ball as target. -/
structure LocalBall (r : ℕ) (x : M) where
  neighborhood : Opens M
  mem_neighborhood : x ∈ neighborhood
  neighborhood_subset_source : (neighborhood : Set M) ⊆ (chartAt E x).source
  radius : ℝ
  radius_pos : 0 < radius
  coord : neighborhood ≃ₘ^(r : ℕ∞ω)⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯
    chartBall (E := E) x radius
  coord_apply (point : neighborhood) :
    (coord point : E) = (chartAt E x) point.1
  coord_symm_apply (point : chartBall (E := E) x radius) :
    ((coord.symm point : neighborhood) : M) = (chartAt E x).symm point.1

namespace LocalBall

variable {r : ℕ} {x : M} (b : LocalBall (𝕜 := 𝕜) (E := E) r x)

/-- The ball target of the coordinate equivalence. -/
abbrev ball : Opens E := chartBall (E := E) x b.radius

@[simp] theorem mem_ball (point : E) :
    point ∈ b.ball ↔ dist point ((chartAt E x) x) < b.radius :=
  mem_chartBall x b.radius point

@[simp] theorem center_mem_ball : (chartAt E x) x ∈ b.ball := by
  exact (b.mem_ball _).2 (by simpa using b.radius_pos)

end LocalBall

section DiffeomorphIso

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN] (IN : ModelWithCorners 𝕜 EN HN)
  {M₀ : Type u} [TopologicalSpace M₀] [ChartedSpace HM M₀]
  {N : Type u} [TopologicalSpace N] [ChartedSpace HN N]

/-- A finite-order diffeomorphism induces an isomorphism of the canonical scalar-function
locally ringed spaces, with maps in both directions induced by the diffeomorphism. -/
def diffeomorphLocallyRingedSpaceIso (r : ℕ)
    (equiv : M₀ ≃ₘ^(r : ℕ∞ω)⟮IM, IN⟯ N) :
    locallyRingedSpace r IM M₀ ≅ locallyRingedSpace r IN N where
  hom := locallyRingedSpaceMap IM IN M₀ N r equiv equiv.contMDiff
  inv := locallyRingedSpaceMap IN IM N M₀ r equiv.symm equiv.symm.contMDiff
  hom_inv_id := by
    rw [← locallyRingedSpaceMap_comp]
    have hfun : (equiv.symm ∘ equiv : M₀ → M₀) = id :=
      funext fun point => equiv.symm_apply_apply point
    simpa only [hfun] using (locallyRingedSpaceMap_id IM M₀ r)
  inv_hom_id := by
    rw [← locallyRingedSpaceMap_comp]
    have hfun : (equiv ∘ equiv.symm : N → N) = id :=
      funext fun point => equiv.apply_symm_apply point
    simpa only [hfun] using (locallyRingedSpaceMap_id IN N r)

variable {IN IM}

/-- The forward arrow is the whole-space map induced by the diffeomorphism. -/
theorem diffeomorphLocallyRingedSpaceIso_hom (r : ℕ)
    (equiv : M₀ ≃ₘ^(r : ℕ∞ω)⟮IM, IN⟯ N) :
    (diffeomorphLocallyRingedSpaceIso IM IN r equiv).hom =
      locallyRingedSpaceMap IM IN M₀ N r equiv equiv.contMDiff := rfl

/-- The backward arrow is the whole-space map induced by the inverse diffeomorphism. -/
theorem diffeomorphLocallyRingedSpaceIso_inv (r : ℕ)
    (equiv : M₀ ≃ₘ^(r : ℕ∞ω)⟮IM, IN⟯ N) :
    (diffeomorphLocallyRingedSpaceIso IM IN r equiv).inv =
      locallyRingedSpaceMap IN IM N M₀ r equiv.symm equiv.symm.contMDiff := rfl

end DiffeomorphIso

/-- Chosen chart coordinates restrict to a finite-order diffeomorphism from an open
neighborhood onto an entire positive-radius ball. -/
def localBall (r : ℕ) [IsManifold 𝓘(𝕜, E) (r : ℕ∞ω) M] (x : M) :
    LocalBall (𝕜 := 𝕜) (E := E) r x := by
  let b := ChartedSpace.chartLocalBall (𝕜 := 𝕜) (E := E) (r : ℕ∞ω) x
  exact {
    neighborhood := b.neighborhood
    mem_neighborhood := b.mem_neighborhood
    neighborhood_subset_source := b.neighborhood_subset_source
    radius := b.radius
    radius_pos := b.radius_pos
    coord := b.coord
    coord_apply := b.coord_apply
    coord_symm_apply := b.coord_symm_apply }

namespace LocalBall

variable {r : ℕ} {x : M} (b : LocalBall (𝕜 := 𝕜) (E := E) r x)

/-- The chart-coordinate isomorphism from the restricted ambient scalar-function
locally ringed space to the scalar-function space on the whole ball. -/
def iso :
    (locallyRingedSpace r 𝓘(𝕜, E) M).restrict b.neighborhood.isOpenEmbedding ≅
      locallyRingedSpace r 𝓘(𝕜, E) b.ball :=
  (restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).trans
    (diffeomorphLocallyRingedSpaceIso 𝓘(𝕜, E) 𝓘(𝕜, E) r b.coord)

/-- The forward LRS arrow factors through restriction followed by the coordinate map. -/
theorem iso_hom : b.iso.hom =
    (restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).hom ≫
      locallyRingedSpaceMap 𝓘(𝕜, E) 𝓘(𝕜, E) b.neighborhood b.ball r
        b.coord b.coord.contMDiff := rfl

/-- The inverse LRS arrow uses the inverse chart after the open-subtype comparison. -/
theorem iso_inv : b.iso.inv =
    locallyRingedSpaceMap 𝓘(𝕜, E) 𝓘(𝕜, E) b.ball b.neighborhood r
        b.coord.symm b.coord.symm.contMDiff ≫
      (restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv := rfl

/-- Transporting the restricted ambient arrow back to intrinsic coordinates
recovers the entire morphism induced by the coordinate diffeomorphism. -/
theorem restrict_iso_inv_comp_iso_hom :
    (restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv ≫ b.iso.hom =
      (diffeomorphLocallyRingedSpaceIso 𝓘(𝕜, E) 𝓘(𝕜, E) r b.coord).hom := by
  rw [b.iso_hom, diffeomorphLocallyRingedSpaceIso_hom]
  simp

/-- The forward LRS arrow acts on points by the restricted chart. -/
@[simp] theorem iso_hom_base (point : b.neighborhood) :
    b.iso.hom.base point = b.coord point := by
  rfl

/-- The inverse LRS arrow acts on points by the inverse restricted chart. -/
@[simp] theorem iso_inv_base (point : b.ball) :
    b.iso.inv.base point = b.coord.symm point := by
  rfl

/-- Coordinate pullback of a germ evaluates the original section at the chart image. -/
theorem coord_germ_eval (U : Opens b.ball) (point : b.neighborhood)
    (hpoint : b.coord point ∈ U)
    (representative : (sheaf 𝓘(𝕜, E) b.ball r).presheaf.obj (op U)) :
    eval 𝓘(𝕜, E) b.neighborhood r point
      ((diffeomorphLocallyRingedSpaceIso 𝓘(𝕜, E) 𝓘(𝕜, E) r b.coord).hom.stalkMap
        point ((sheaf 𝓘(𝕜, E) b.ball r).presheaf.germ U (b.coord point)
          hpoint representative)) = representative ⟨b.coord point, hpoint⟩ := by
  change eval 𝓘(𝕜, E) b.neighborhood r point
    ((locallyRingedSpaceMap 𝓘(𝕜, E) 𝓘(𝕜, E) b.neighborhood b.ball r
      b.coord b.coord.contMDiff).stalkMap point
      ((sheaf 𝓘(𝕜, E) b.ball r).presheaf.germ U (b.coord point)
        hpoint representative)) = _
  rw [stalkMap_germ]
  exact (eval_germ (IM := 𝓘(𝕜, E)) (M := b.neighborhood) r
    (ContinuousFunctions.inverseImage b.neighborhood b.ball b.coord
      b.coord.contMDiff.continuous U) point hpoint
    (precompose 𝓘(𝕜, E) 𝓘(𝕜, E) b.neighborhood b.ball r b.coord
      b.coord.contMDiff U representative)).trans
    (precompose_apply 𝓘(𝕜, E) 𝓘(𝕜, E) b.neighborhood b.ball r
      b.coord b.coord.contMDiff U representative ⟨point, hpoint⟩)

/-- A germ pulled through the restricted ambient coordinate arrow evaluates at
the chart image after transport back to the intrinsic neighborhood stalk. -/
theorem iso_hom_germ_eval (U : Opens b.ball) (point : b.neighborhood)
    (hpoint : b.coord point ∈ U)
    (representative : (sheaf 𝓘(𝕜, E) b.ball r).presheaf.obj (op U)) :
    eval 𝓘(𝕜, E) b.neighborhood r point
      ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv.stalkMap point
        (b.iso.hom.stalkMap
          ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv.base point)
          ((sheaf 𝓘(𝕜, E) b.ball r).presheaf.germ U (b.coord point)
            hpoint representative))) = representative ⟨b.coord point, hpoint⟩ := by
  change eval 𝓘(𝕜, E) b.neighborhood r point
    ((b.iso.hom.stalkMap
      ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv.base point) ≫
        (restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv.stalkMap point)
      ((sheaf 𝓘(𝕜, E) b.ball r).presheaf.germ U (b.coord point)
        hpoint representative)) = _
  rw [← LocallyRingedSpace.stalkMap_comp]
  have hmap := LocallyRingedSpace.stalkMap_congr_hom
    ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv ≫ b.iso.hom)
    (diffeomorphLocallyRingedSpaceIso 𝓘(𝕜, E) 𝓘(𝕜, E) r b.coord).hom
    b.restrict_iso_inv_comp_iso_hom point
  have hbase :
      (diffeomorphLocallyRingedSpaceIso 𝓘(𝕜, E) 𝓘(𝕜, E) r b.coord).hom.base point =
        ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv ≫
          b.iso.hom).base point := rfl
  have hspecializes :
      (locallyRingedSpace r 𝓘(𝕜, E) b.ball).presheaf.stalkSpecializes
        (specializes_of_eq hbase) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [hspecializes] at hmap
  rw [hmap]
  exact b.coord_germ_eval U point hpoint representative

/-- The composite's pullback of a section evaluates, as a germ in the intrinsic
neighborhood, at the original section's chart image. -/
theorem iso_hom_section_germ_eval (U : Opens b.ball) (point : b.neighborhood)
    (hpoint : b.coord point ∈ U)
    (representative : (sheaf 𝓘(𝕜, E) b.ball r).presheaf.obj (op U)) :
    eval 𝓘(𝕜, E) b.neighborhood r point
      ((sheaf 𝓘(𝕜, E) b.neighborhood r).presheaf.germ
        ((Opens.map ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r
          b.neighborhood).inv ≫ b.iso.hom).base).obj U)
        point hpoint
        (((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv ≫
          b.iso.hom).c.app (op U) representative)) =
      representative ⟨b.coord point, hpoint⟩ := by
  change eval 𝓘(𝕜, E) b.neighborhood r point
    ((locallyRingedSpace r 𝓘(𝕜, E) b.neighborhood).presheaf.germ
      ((Opens.map ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r
        b.neighborhood).inv ≫ b.iso.hom).base).obj U)
      point hpoint
      (((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv ≫
        b.iso.hom).c.app (op U) representative)) = _
  have hsection := LocallyRingedSpace.stalkMap_germ_apply
    ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv ≫
      b.iso.hom) U point hpoint representative
  calc
    _ = eval 𝓘(𝕜, E) b.neighborhood r point
          (((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv ≫
            b.iso.hom).stalkMap point
            ((sheaf 𝓘(𝕜, E) b.ball r).presheaf.germ U (b.coord point)
              hpoint representative)) :=
      congrArg (eval 𝓘(𝕜, E) b.neighborhood r point) hsection.symm
    _ = _ := by
      rw [LocallyRingedSpace.stalkMap_comp]
      change eval 𝓘(𝕜, E) b.neighborhood r point
        ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv.stalkMap point
          (b.iso.hom.stalkMap
            ((restrictLocallyRingedSpaceIso 𝓘(𝕜, E) M r b.neighborhood).inv.base point)
            ((sheaf 𝓘(𝕜, E) b.ball r).presheaf.germ U (b.coord point)
              hpoint representative))) = _
      exact b.iso_hom_germ_eval U point hpoint representative

end LocalBall

end FiniteRegularityFunctions
