/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.ChartedSpace.LocalBall
public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace

/-!
# Smooth scalar-function spaces in chart-ball coordinates

The canonical locally ringed space of smooth scalar functions, restricted from an
ambient smooth manifold to a chart neighborhood, is compared with the canonical
smooth scalar-function space on the entire model ball.

## Implementation notes

The pinned Mathlib smooth sheaf API puts the scalar field, model space and manifold
carrier in one universe, whereas the underlying `ChartLocalBall` geometry permits
three independent universes. This comparison runs from the restricted ambient
canonical smooth scalar locally ringed space to the entire-ball canonical one;
it asserts neither an analytic identification nor a converse for arbitrary sheaves.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025
  draft), Definition 4.3.9 (p. 142): motivation for local smooth-function ball models,
  not a proof of this whole canonical smooth scalar locally ringed space comparison or a
  reconstruction of an arbitrary structure sheaf.
* Mathlib, `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean` (Heather Macbeth and
  Adam Topaz) and `Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean`
  (Heather Macbeth): the canonical scalar sheaf and locally ringed space
  compared using the project chart-ball geometry.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

universe u

namespace ChartedSpace.ChartLocalBall

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {x : M} (b : ChartLocalBall (𝕜 := 𝕜) (E := E) (∞ : ℕ∞ω) x)

/-- Comparison from the restricted ambient smooth scalar locally ringed space
to the canonical smooth scalar locally ringed space on the entire chart ball. -/
def smoothIso :
    (locallyRingedSpace 𝓘(𝕜, E) M).restrict b.neighborhood.isOpenEmbedding ≅
      locallyRingedSpace 𝓘(𝕜, E) b.ball :=
  (restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M) b.neighborhood).trans
    { hom := locallyRingedSpaceMap b.coord b.coord.contMDiff
      inv := locallyRingedSpaceMap b.coord.symm b.coord.symm.contMDiff
      hom_inv_id := by
        rw [← locallyRingedSpace_comp]
        have hfun : (b.coord.symm ∘ b.coord : b.neighborhood → b.neighborhood) = id :=
          funext fun point => b.coord.symm_apply_apply point
        simpa only [hfun] using (locallyRingedSpace_id 𝓘(𝕜, E) b.neighborhood)
      inv_hom_id := by
        rw [← locallyRingedSpace_comp]
        have hfun : (b.coord ∘ b.coord.symm : b.ball → b.ball) = id :=
          funext fun point => b.coord.apply_symm_apply point
        simpa only [hfun] using (locallyRingedSpace_id 𝓘(𝕜, E) b.ball) }

/-- The whole forward morphism factors through Mathlib's canonical open restriction. -/
theorem smoothIso_hom : b.smoothIso.hom =
    (restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M) b.neighborhood).hom ≫
      locallyRingedSpaceMap b.coord b.coord.contMDiff := rfl

/-- The inverse whole morphism first applies the inverse chart, then ambient restriction. -/
theorem smoothIso_inv : b.smoothIso.inv =
    locallyRingedSpaceMap b.coord.symm b.coord.symm.contMDiff ≫
      (restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M) b.neighborhood).inv := rfl

/-- Returning from restricted ambient coordinates recovers the whole chart morphism. -/
theorem restrict_smoothIso_hom :
    (restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M) b.neighborhood).inv ≫
      b.smoothIso.hom =
      locallyRingedSpaceMap b.coord b.coord.contMDiff := by
  simp only [b.smoothIso_hom, Iso.inv_hom_id_assoc]

/-- The full composite has the chart-coordinate map as its base map. -/
@[simp] theorem restrict_smoothIso_hom_base (point : b.neighborhood) :
    ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
      b.neighborhood).inv ≫ b.smoothIso.hom).base point = b.coord point := by
  rw [b.restrict_smoothIso_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem restrictIso_inv_base (point : b.neighborhood) :
    (restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
      b.neighborhood).inv.base point = point := by
  apply Subtype.ext
  have hfac := LocallyRingedSpace.IsOpenImmersion.lift_fac
    ((locallyRingedSpace 𝓘(𝕜, E) M).ofRestrict b.neighborhood.isOpenEmbedding)
    (locallyRingedSpaceMap (IM := 𝓘(𝕜, E)) (IN := 𝓘(𝕜, E))
      (fun sourcePoint : b.neighborhood => (sourcePoint : M)) contMDiff_subtype_val)
    (by rfl)
  change (restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
    b.neighborhood).inv ≫
      (locallyRingedSpace 𝓘(𝕜, E) M).ofRestrict b.neighborhood.isOpenEmbedding =
    locallyRingedSpaceMap (IM := 𝓘(𝕜, E)) (IN := 𝓘(𝕜, E))
      (fun sourcePoint : b.neighborhood => (sourcePoint : M))
      contMDiff_subtype_val at hfac
  have hinclusion (restrictedPoint : b.neighborhood) :
      ((locallyRingedSpace 𝓘(𝕜, E) M).ofRestrict
        b.neighborhood.isOpenEmbedding).base restrictedPoint =
          (restrictedPoint : M) := rfl
  have hcoord :
      (locallyRingedSpaceMap (IM := 𝓘(𝕜, E)) (IN := 𝓘(𝕜, E))
        (fun sourcePoint : b.neighborhood => (sourcePoint : M))
        contMDiff_subtype_val).base point = (point : M) := rfl
  have hbase := congrArg (fun morphism => morphism.base point) hfac
  rw [LocallyRingedSpace.comp_base, CategoryTheory.comp_apply] at hbase
  rw [hinclusion, hcoord] at hbase
  set_option backward.isDefEq.respectTransparency true in
    exact hbase

/-- The forward map on points is the chart coordinate map. -/
@[simp] theorem smoothIso_hom_base (point : b.neighborhood) :
    b.smoothIso.hom.base point = b.coord point := by
  have hbase := b.restrict_smoothIso_hom_base point
  change b.smoothIso.hom.base
    ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
      b.neighborhood).inv.base point) = b.coord point at hbase
  simpa only [b.restrictIso_inv_base] using hbase

/-- The inverse map on points is the inverse chart coordinate map. -/
@[simp] theorem smoothIso_inv_base (point : b.ball) :
    b.smoothIso.inv.base point = b.coord.symm point := by
  rw [b.smoothIso_inv]
  rw [LocallyRingedSpace.comp_base]
  change (restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
    b.neighborhood).inv.base (b.coord.symm point) = b.coord.symm point
  exact b.restrictIso_inv_base _

/-- Evaluation of a germ pulled through the full restricted-ambient composite. -/
theorem smoothIso_hom_germ_eval (V : Opens b.ball) (point : b.neighborhood)
    (hpoint : b.coord point ∈ V)
    (representative : (smoothSheafCommRing 𝓘(𝕜, E) 𝓘(𝕜) b.ball 𝕜).presheaf.obj (op V)) :
    smoothSheafCommRing.eval 𝓘(𝕜, E) 𝓘(𝕜) b.neighborhood 𝕜 point
      (((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
        b.neighborhood).inv ≫
        b.smoothIso.hom).stalkMap point
          ((smoothSheafCommRing 𝓘(𝕜, E) 𝓘(𝕜) b.ball 𝕜).presheaf.germ V
            (((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
              b.neighborhood).inv ≫ b.smoothIso.hom).base point)
            (by simpa only [b.restrict_smoothIso_hom_base] using hpoint)
            representative)) =
      representative ⟨b.coord point, hpoint⟩ := by
  have heval :
      ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
        b.neighborhood).inv ≫ b.smoothIso.hom).stalkMap point ≫
          smoothSheafCommRing.evalHom 𝓘(𝕜, E) 𝓘(𝕜) b.neighborhood 𝕜 point =
        smoothSheafCommRing.evalHom 𝓘(𝕜, E) 𝓘(𝕜) b.ball 𝕜
          (((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
            b.neighborhood).inv ≫ b.smoothIso.hom).base point) := by
    rw [b.restrict_smoothIso_hom]
    exact stalkMap_locallyRingedSpaceMap_evalHom b.coord b.coord.contMDiff point
  calc
    _ = smoothSheafCommRing.evalHom 𝓘(𝕜, E) 𝓘(𝕜) b.ball 𝕜
          (((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
            b.neighborhood).inv ≫ b.smoothIso.hom).base point)
          ((smoothSheafCommRing 𝓘(𝕜, E) 𝓘(𝕜) b.ball 𝕜).presheaf.germ V
            (((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
              b.neighborhood).inv ≫ b.smoothIso.hom).base point)
            (by simpa only [b.restrict_smoothIso_hom_base] using hpoint)
            representative) := by
      exact congr($(heval)
          ((smoothSheafCommRing 𝓘(𝕜, E) 𝓘(𝕜) b.ball 𝕜).presheaf.germ V
            (((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
              b.neighborhood).inv ≫ b.smoothIso.hom).base point)
            (by simpa only [b.restrict_smoothIso_hom_base] using hpoint)
            representative))
    _ = _ := by
      rw [smoothSheafCommRing.evalHom_germ]
      exact congrArg representative (Subtype.ext (b.restrict_smoothIso_hom_base point))

/-- Evaluation of a pulled-back section as a germ through the full composite. -/
theorem smoothIso_hom_section_germ_eval (V : Opens b.ball) (point : b.neighborhood)
    (hpoint : b.coord point ∈ V)
    (representative : (smoothSheafCommRing 𝓘(𝕜, E) 𝓘(𝕜) b.ball 𝕜).presheaf.obj (op V)) :
    smoothSheafCommRing.eval 𝓘(𝕜, E) 𝓘(𝕜) b.neighborhood 𝕜 point
      ((smoothSheafCommRing 𝓘(𝕜, E) 𝓘(𝕜) b.neighborhood 𝕜).presheaf.germ
        ((Opens.map ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
          b.neighborhood).inv ≫
          b.smoothIso.hom).base).obj V)
        point (by
          change ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
            b.neighborhood).inv ≫ b.smoothIso.hom).base point ∈ V
          simpa only [b.restrict_smoothIso_hom_base] using hpoint)
        (((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
          b.neighborhood).inv ≫
          b.smoothIso.hom).c.app (op V) representative)) =
      representative ⟨b.coord point, hpoint⟩ := by
  have hpoint' : ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
      b.neighborhood).inv ≫ b.smoothIso.hom).base point ∈ V := by
    simpa only [b.restrict_smoothIso_hom_base] using hpoint
  have hsection := LocallyRingedSpace.stalkMap_germ_apply
    ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
      b.neighborhood).inv ≫ b.smoothIso.hom) V point
      hpoint' representative
  change smoothSheafCommRing.eval 𝓘(𝕜, E) 𝓘(𝕜) b.neighborhood 𝕜 point
    ((locallyRingedSpace 𝓘(𝕜, E) b.neighborhood).presheaf.germ
      ((Opens.map ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
        b.neighborhood).inv ≫ b.smoothIso.hom).base).obj V)
      point hpoint'
      (((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
        b.neighborhood).inv ≫ b.smoothIso.hom).c.app (op V) representative)) = _
  exact (congrArg (smoothSheafCommRing.eval 𝓘(𝕜, E) 𝓘(𝕜)
    b.neighborhood 𝕜 point) hsection.symm).trans
      (b.smoothIso_hom_germ_eval V point hpoint representative)

end ChartedSpace.ChartLocalBall
