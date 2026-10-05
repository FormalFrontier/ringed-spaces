/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.ChartedSpace.CompatibleAtlases
public import RingedSpaces.ChartedSpace.SmoothScalarReconstruction

/-!
# Smooth scalar sheaves for compatible atlases

Two explicitly specified compatible atlases on the same topological carrier determine
canonically isomorphic locally ringed spaces of smooth scalar functions. The isomorphism
has the identity as its base map and precomposes every section with the identity.

The scalar field and carrier share the universe required by the existing smooth sheaf;
the model and chart spaces may live in independent universes. No finiteness, separation,
or nonemptiness assumptions are imposed.

## References

* Mathlib, `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean` (Heather Macbeth and
  Adam Topaz) and `Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean`
  (Heather Macbeth): the existing smooth scalar sheaf and locally ringed space
  compared under the two atlases.
* `RingedSpaces.ChartedSpace.CompatibleAtlases`: the compatible maximal-atlas
  comparison used to identify the smooth structures.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025
  draft), Definition 4.3.9 (p. 142): motivation for local-model independence,
  not a proof of the canonical identity-base whole scalar-sheaf comparison of
  two specified atlases, arbitrary-sheaf recovery or automatic complex scalar preservation.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

universe u v w

namespace ChartedSpace

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type w} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H)
  {M : Type u} [TopologicalSpace M]

/-- The canonical smooth scalar locally ringed space for a specified atlas. -/
def smoothScalarLocallyRingedSpace (C : ChartedSpace H M) : LocallyRingedSpace := by
  letI : ChartedSpace H M := C
  exact locallyRingedSpace I M

@[simp] theorem smoothScalarLocallyRingedSpace_carrier (C : ChartedSpace H M) :
    (smoothScalarLocallyRingedSpace I C).carrier = ↧M := rfl

/-- Mixed smooth transitions make the identity smooth from the first specified
atlas to the second, with neither atlas assumed independently regular. -/
theorem contMDiff_id_of_compatible_atlases (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) :
    @ContMDiff 𝕜 _ E _ _ H _ I M _ C₀ E _ _ H _ I M _ C₁ ∞ (id : M → M) := by
  intro point
  apply (@contMDiffAt_iff 𝕜 _ E _ _ H _ I M _ C₀ E _ _ H _ I M _ C₁
    ∞ (id : M → M) point).2
  refine ⟨continuousAt_id, ?_⟩
  have hchange : ContDiffWithinAt 𝕜 ∞
      (I.extendCoordChange (C₀.chartAt point) (C₁.chartAt point))
      (Set.range I) ((C₀.chartAt point).extend I point) := by
    let : ChartedSpace H M := C₁
    let : HasGroupoid M (contDiffGroupoid ∞ I) :=
      (hasGroupoid_of_compatible_atlases (contDiffGroupoid ∞ I) C₀ C₁ h).2
    have he : C₀.chartAt point ∈
        @StructureGroupoid.maximalAtlas H M _ _ C₁ (contDiffGroupoid ∞ I) := by
      rw [← maximalAtlas_eq_of_compatible_atlases (contDiffGroupoid ∞ I) C₀ C₁ h]
      let : ChartedSpace H M := C₀
      let : HasGroupoid M (contDiffGroupoid ∞ I) :=
        (hasGroupoid_of_compatible_atlases (contDiffGroupoid ∞ I) C₀ C₁ h).1
      exact (contDiffGroupoid ∞ I).subset_maximalAtlas (C₀.chart_mem_atlas point)
    exact I.contDiffWithinAt_extendCoordChange' he
      ((contDiffGroupoid ∞ I).subset_maximalAtlas (C₁.chart_mem_atlas point))
      (C₀.mem_chart_source point) (C₁.mem_chart_source point)
  change ContDiffWithinAt 𝕜 ∞
    (I.extendCoordChange (C₀.chartAt point) (C₁.chartAt point))
    (Set.range I) ((C₀.chartAt point).extend I point)
  exact hchange

/-- Mixed smooth compatibility is symmetric, with the same specified atlases. -/
theorem compatible_atlases_symm (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) :
    ∀ e ∈ C₁.atlas, ∀ f ∈ C₀.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I := by
  intro e he f hf
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] using (contDiffGroupoid ∞ I).symm (h f hf e he)

/-- The identity-base isomorphism of the two canonical smooth scalar locally ringed spaces.
Its entire forward and inverse morphisms are induced by smooth precomposition. -/
def compatibleAtlasLocallyRingedSpaceIso (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) :
    smoothScalarLocallyRingedSpace I C₀ ≅ smoothScalarLocallyRingedSpace I C₁ := by
  let hrev := compatible_atlases_symm I C₀ C₁ h
  refine {
    hom := @locallyRingedSpaceMap 𝕜 _ E _ _ H _ I M _ C₀ E _ _ H _ I M _ C₁
      id (contMDiff_id_of_compatible_atlases I C₀ C₁ h)
    inv := @locallyRingedSpaceMap 𝕜 _ E _ _ H _ I M _ C₁ E _ _ H _ I M _ C₀
      id (contMDiff_id_of_compatible_atlases I C₁ C₀ hrev)
    hom_inv_id := by
      rfl
    inv_hom_id := by
      rfl }

/-- The entire forward locally ringed-space morphism is Mathlib's smooth pullback. -/
theorem compatibleAtlasLocallyRingedSpaceIso_hom (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) :
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom =
      @locallyRingedSpaceMap 𝕜 _ E _ _ H _ I M _ C₀ E _ _ H _ I M _ C₁
        id (contMDiff_id_of_compatible_atlases I C₀ C₁ h) := rfl

/-- The entire inverse locally ringed-space morphism is smooth pullback in reverse. -/
theorem compatibleAtlasLocallyRingedSpaceIso_inv (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) :
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv =
      @locallyRingedSpaceMap 𝕜 _ E _ _ H _ I M _ C₁ E _ _ H _ I M _ C₀
        id (contMDiff_id_of_compatible_atlases I C₁ C₀
          (compatible_atlases_symm I C₀ C₁ h)) := rfl

/-- The entire forward base arrow is the identity of the original carrier. -/
@[simp] theorem compatibleAtlasLocallyRingedSpaceIso_hom_base_eq
    (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) :
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.base = 𝟙 (TopCat.of M) := rfl

/-- The entire inverse base arrow is the identity of the original carrier. -/
@[simp] theorem compatibleAtlasLocallyRingedSpaceIso_inv_base_eq
    (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) :
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.base = 𝟙 (TopCat.of M) := rfl

/-- The forward isomorphism is the identity on the original topological carrier. -/
@[simp] theorem compatibleAtlasLocallyRingedSpaceIso_hom_base (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (point : M) :
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.base point = point := rfl

/-- The inverse isomorphism is the identity on the original topological carrier. -/
@[simp] theorem compatibleAtlasLocallyRingedSpaceIso_inv_base (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (point : M) :
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.base point = point := rfl

/-- On every open, the full forward sheaf component preserves each function value. -/
@[simp] theorem compatibleAtlasLocallyRingedSpaceIso_hom_apply (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (representative : (smoothScalarLocallyRingedSpace I C₁).presheaf.obj (op U)) (point : U) :
    (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.c.app (op U)) representative).1
        point = representative.1 point := rfl

/-- On every open, the full inverse sheaf component preserves each function value. -/
@[simp] theorem compatibleAtlasLocallyRingedSpaceIso_inv_apply (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (representative : (smoothScalarLocallyRingedSpace I C₀).presheaf.obj (op U)) (point : U) :
    (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.c.app (op U)) representative).1
        point = representative.1 point := rfl

/-- The forward comparison on any original open set as an equivalence of section rings. -/
def compatibleAtlasSectionRingEquiv (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M) :
    (smoothScalarLocallyRingedSpace I C₁).presheaf.obj (op U) ≃+*
      (smoothScalarLocallyRingedSpace I C₀).presheaf.obj (op U) := by
  exact RingEquiv.ofBijective
    ((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.c.app (op U)).hom (by
      constructor
      · intro representative other heq
        apply Subtype.ext
        funext point
        have hpoint := congrArg (fun value => value.1 point) heq
        calc
          representative.1 point =
              (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.c.app (op U))
                representative).1 point :=
            (compatibleAtlasLocallyRingedSpaceIso_hom_apply I C₀ C₁ h U
              representative point).symm
          _ = (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.c.app (op U))
                other).1 point := hpoint
          _ = other.1 point :=
            compatibleAtlasLocallyRingedSpaceIso_hom_apply I C₀ C₁ h U other point
      · intro representative
        refine ⟨((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.c.app (op U))
          representative, ?_⟩
        apply Subtype.ext
        funext point
        rfl)

/-- The section-ring equivalence is the complete forward sheaf component. -/
theorem compatibleAtlasSectionRingEquiv_eq_hom (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (representative : (smoothScalarLocallyRingedSpace I C₁).presheaf.obj (op U)) :
    compatibleAtlasSectionRingEquiv I C₀ C₁ h U representative =
      ((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.c.app (op U)) representative := rfl

/-- The equivalence sends every smooth section to the same scalar function. -/
@[simp] theorem compatibleAtlasSectionRingEquiv_apply (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (representative : (smoothScalarLocallyRingedSpace I C₁).presheaf.obj (op U)) (point : U) :
    (compatibleAtlasSectionRingEquiv I C₀ C₁ h U representative).1 point =
      representative.1 point := by
  rw [compatibleAtlasSectionRingEquiv_eq_hom]
  exact compatibleAtlasLocallyRingedSpaceIso_hom_apply I C₀ C₁ h U representative point

/-- The inverse section equivalence is the inverse full sheaf component on every open. -/
theorem compatibleAtlasSectionRingEquiv_symm_eq_inv (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (representative : (smoothScalarLocallyRingedSpace I C₀).presheaf.obj (op U)) :
    (compatibleAtlasSectionRingEquiv I C₀ C₁ h U).symm representative =
      ((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.c.app (op U)) representative := by
  apply Subtype.ext
  funext point
  calc
    _ = representative.1 point := by
      simpa only [RingEquiv.apply_symm_apply] using
        (compatibleAtlasSectionRingEquiv_apply I C₀ C₁ h U
          ((compatibleAtlasSectionRingEquiv I C₀ C₁ h U).symm representative) point).symm
    _ = _ := (compatibleAtlasLocallyRingedSpaceIso_inv_apply I C₀ C₁ h U
      representative point).symm

/-- The inverse equivalence preserves every value of a smooth section. -/
@[simp] theorem compatibleAtlasSectionRingEquiv_symm_apply (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (representative : (smoothScalarLocallyRingedSpace I C₀).presheaf.obj (op U)) (point : U) :
    ((compatibleAtlasSectionRingEquiv I C₀ C₁ h U).symm representative).1 point =
      representative.1 point := by
  rw [compatibleAtlasSectionRingEquiv_symm_eq_inv]
  exact compatibleAtlasLocallyRingedSpaceIso_inv_apply I C₀ C₁ h U representative point

/-- On nested original opens, the equivalence commutes with restriction. -/
theorem compatibleAtlasSectionRingEquiv_restrict (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) {U V : Opens M} (hVU : V ≤ U)
    (representative : (smoothScalarLocallyRingedSpace I C₁).presheaf.obj (op U)) :
    (smoothScalarLocallyRingedSpace I C₀).presheaf.map (homOfLE hVU).op
        (compatibleAtlasSectionRingEquiv I C₀ C₁ h U representative) =
      compatibleAtlasSectionRingEquiv I C₀ C₁ h V
        ((smoothScalarLocallyRingedSpace I C₁).presheaf.map (homOfLE hVU).op
          representative) := by
  apply Subtype.ext
  funext point
  rfl

/-- The inverse full sheaf component also commutes with every restriction. -/
theorem compatibleAtlasLocallyRingedSpaceIso_inv_restrict (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) {U V : Opens M} (hVU : V ≤ U)
    (representative : (smoothScalarLocallyRingedSpace I C₀).presheaf.obj (op U)) :
    (smoothScalarLocallyRingedSpace I C₁).presheaf.map (homOfLE hVU).op
        (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.c.app (op U))
          representative) =
      ((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.c.app (op V))
        ((smoothScalarLocallyRingedSpace I C₀).presheaf.map (homOfLE hVU).op
          representative) := by
  apply Subtype.ext
  funext point
  rfl

/-- Restriction commutes with the inverse equivalence on nested original opens. -/
theorem compatibleAtlasSectionRingEquiv_symm_restrict (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) {U V : Opens M} (hVU : V ≤ U)
    (representative : (smoothScalarLocallyRingedSpace I C₀).presheaf.obj (op U)) :
    (smoothScalarLocallyRingedSpace I C₁).presheaf.map (homOfLE hVU).op
        ((compatibleAtlasSectionRingEquiv I C₀ C₁ h U).symm representative) =
      (compatibleAtlasSectionRingEquiv I C₀ C₁ h V).symm
        ((smoothScalarLocallyRingedSpace I C₀).presheaf.map (homOfLE hVU).op
          representative) := by
  rw [compatibleAtlasSectionRingEquiv_symm_eq_inv I C₀ C₁ h U representative]
  rw [compatibleAtlasSectionRingEquiv_symm_eq_inv I C₀ C₁ h V
    ((smoothScalarLocallyRingedSpace I C₀).presheaf.map (homOfLE hVU).op
      representative)]
  exact compatibleAtlasLocallyRingedSpaceIso_inv_restrict I C₀ C₁ h hVU representative

/-- A scalar constant as a section for an explicitly specified atlas. -/
def smoothScalarConstant (C : ChartedSpace H M) (U : Opens M) (scalar : 𝕜) :
    (smoothScalarLocallyRingedSpace I C).presheaf.obj (op U) := by
  letI : ChartedSpace H M := C
  exact ContMDiffMap.C (I := I) (N := U) (A := 𝕜) (n := ∞) scalar

@[simp] theorem smoothScalarConstant_apply (C : ChartedSpace H M)
    (U : Opens M) (scalar : 𝕜) (point : U) :
    (smoothScalarConstant I C U scalar).1 point = scalar := rfl

/-- Both sheaves identify the same chosen scalar constants on every original open. -/
theorem compatibleAtlasSectionRingEquiv_constant (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M) (scalar : 𝕜) :
    compatibleAtlasSectionRingEquiv I C₀ C₁ h U (smoothScalarConstant I C₁ U scalar) =
      smoothScalarConstant I C₀ U scalar := by
  apply Subtype.ext
  funext point
  simp only [compatibleAtlasSectionRingEquiv_apply, smoothScalarConstant_apply]

/-- The inverse equivalence preserves chosen scalar constants on every original open. -/
theorem compatibleAtlasSectionRingEquiv_symm_constant (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M) (scalar : 𝕜) :
    (compatibleAtlasSectionRingEquiv I C₀ C₁ h U).symm
        (smoothScalarConstant I C₀ U scalar) =
      smoothScalarConstant I C₁ U scalar := by
  apply Subtype.ext
  funext point
  simp only [compatibleAtlasSectionRingEquiv_symm_apply, smoothScalarConstant_apply]

/-- Evaluate a smooth scalar germ with the atlas explicitly indexed. -/
def smoothScalarStalkEval (C : ChartedSpace H M) (point : M) :
    (smoothScalarLocallyRingedSpace I C).presheaf.stalk point →+* 𝕜 := by
  letI : ChartedSpace H M := C
  exact smoothSheafCommRing.eval I 𝓘(𝕜) M 𝕜 point

@[simp] theorem smoothScalarStalkEval_germ (C : ChartedSpace H M) (U : Opens M)
    (point : M) (hpoint : point ∈ U)
    (representative : (smoothScalarLocallyRingedSpace I C).presheaf.obj (op U)) :
    smoothScalarStalkEval I C point
      ((smoothScalarLocallyRingedSpace I C).presheaf.germ U point hpoint representative) =
      representative.1 ⟨point, hpoint⟩ := by
  let : ChartedSpace H M := C
  exact smoothSheafCommRing.eval_germ U point hpoint representative

/-- Forward transport of the germ of any smooth section is its pulled-back germ. -/
theorem compatibleAtlasLocallyRingedSpaceIso_hom_germ (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (point : M) (hpoint : point ∈ U)
    (representative : (smoothScalarLocallyRingedSpace I C₁).presheaf.obj (op U)) :
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.stalkMap point
        ((smoothScalarLocallyRingedSpace I C₁).presheaf.germ U point hpoint representative) =
      (smoothScalarLocallyRingedSpace I C₀).presheaf.germ U point hpoint
        (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.c.app (op U))
          representative) := by
  exact LocallyRingedSpace.stalkMap_germ_apply
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom U point hpoint representative

/-- Inverse transport of the germ of any smooth section is its pulled-back germ. -/
theorem compatibleAtlasLocallyRingedSpaceIso_inv_germ (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (point : M) (hpoint : point ∈ U)
    (representative : (smoothScalarLocallyRingedSpace I C₀).presheaf.obj (op U)) :
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.stalkMap point
        ((smoothScalarLocallyRingedSpace I C₀).presheaf.germ U point hpoint representative) =
      (smoothScalarLocallyRingedSpace I C₁).presheaf.germ U point hpoint
        (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.c.app (op U))
          representative) := by
  exact LocallyRingedSpace.stalkMap_germ_apply
    (compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv U point hpoint representative

/-- The full forward stalk map preserves evaluation of germs on every original open. -/
theorem compatibleAtlasLocallyRingedSpaceIso_hom_germ_eval (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (point : M) (hpoint : point ∈ U)
    (representative : (smoothScalarLocallyRingedSpace I C₁).presheaf.obj (op U)) :
    smoothScalarStalkEval I C₀ point
      ((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.stalkMap point
        ((smoothScalarLocallyRingedSpace I C₁).presheaf.germ U point hpoint representative)) =
      representative.1 ⟨point, hpoint⟩ := by
  calc
    _ = (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.c.app (op U))
          representative).1 ⟨point, hpoint⟩ :=
      (congrArg (smoothScalarStalkEval I C₀ point)
        (compatibleAtlasLocallyRingedSpaceIso_hom_germ I C₀ C₁ h U point hpoint
          representative)).trans
        (smoothScalarStalkEval_germ I C₀ U point hpoint
          (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).hom.c.app (op U))
            representative))
    _ = representative.1 ⟨point, hpoint⟩ :=
      compatibleAtlasLocallyRingedSpaceIso_hom_apply I C₀ C₁ h U representative
        ⟨point, hpoint⟩

/-- The full inverse stalk map preserves evaluation of germs on every original open. -/
theorem compatibleAtlasLocallyRingedSpaceIso_inv_germ_eval (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid ∞ I) (U : Opens M)
    (point : M) (hpoint : point ∈ U)
    (representative : (smoothScalarLocallyRingedSpace I C₀).presheaf.obj (op U)) :
    smoothScalarStalkEval I C₁ point
      ((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.stalkMap point
        ((smoothScalarLocallyRingedSpace I C₀).presheaf.germ U point hpoint representative)) =
      representative.1 ⟨point, hpoint⟩ := by
  calc
    _ = (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.c.app (op U))
          representative).1 ⟨point, hpoint⟩ :=
      (congrArg (smoothScalarStalkEval I C₁ point)
        (compatibleAtlasLocallyRingedSpaceIso_inv_germ I C₀ C₁ h U point hpoint
          representative)).trans
        (smoothScalarStalkEval_germ I C₁ U point hpoint
          (((compatibleAtlasLocallyRingedSpaceIso I C₀ C₁ h).inv.c.app (op U))
            representative))
    _ = representative.1 ⟨point, hpoint⟩ :=
      compatibleAtlasLocallyRingedSpaceIso_inv_apply I C₀ C₁ h U representative
        ⟨point, hpoint⟩

end ChartedSpace
