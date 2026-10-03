/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Restriction
public import RingedSpaces.OpenCover
public import RingedSpacesTests.OpenCover

/-!
# Direct-import clients for literal open-intersection gluing

These checks use full ringed-space morphisms through the public restriction, pullback
and gluing APIs, without the private lifting implementation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Test.Restriction

universe u

variable {X Y : RingedSpace.{u, u}} (U V : Opens X)

/-- The restriction map is the literal inclusion on underlying points. -/
theorem literalInclusion (h : U ≤ V) (t : U) :
    (RingedSpace.restrictMap U V h).hom.base t = ⟨t.1, h t.2⟩ :=
  RingedSpace.restrictMap_base U V h t

/-- Restriction along an identity inclusion is the identity full morphism. -/
theorem identityRestriction :
    RingedSpace.restrictMap U U le_rfl = 𝟙 _ :=
  RingedSpace.restrictMap_id U

/-- The full restriction maps are functorial along chains of inclusions. -/
theorem composedRestriction {W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) :
    RingedSpace.restrictMap U V hUV ≫ RingedSpace.restrictMap V W hVW =
      RingedSpace.restrictMap U W (hUV.trans hVW) :=
  RingedSpace.restrictMap_comp U V hUV hVW

/-- The factorization is an equality of full morphisms, not merely continuous maps. -/
theorem fullFactorization (h : U ≤ V) :
    RingedSpace.restrictMap U V h ≫ X.ofRestrict V.isOpenEmbedding =
      X.ofRestrict U.isOpenEmbedding :=
  RingedSpace.restrictMap_ofRestrict U V h

/-- The factorization agrees even as a presheafed-space morphism, so in particular
its structure-sheaf transformation is not merely inferred from the carrier map. -/
theorem sheafComponent (h : U ≤ V) :
    (RingedSpace.restrictMap U V h ≫ X.ofRestrict V.isOpenEmbedding).hom =
      (X.ofRestrict U.isOpenEmbedding).hom :=
  congrArg InducedCategory.Hom.hom (fullFactorization U V h)

/-- The literal intersection is a categorical pullback as a full ringed space. -/
theorem literalPullback :
    IsPullback
      (RingedSpace.restrictMap (U ⊓ V) U inf_le_left)
      (RingedSpace.restrictMap (U ⊓ V) V inf_le_right)
      (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) :=
  RingedSpace.isPullback_restrictInf U V

/-- Pullback comparison genuinely identifies both full projections. -/
theorem literalProjectionLeft :
    (RingedSpace.isPullback_restrictInf U V).isoPullback.hom ≫
      pullback.fst (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) =
      RingedSpace.restrictMap (U ⊓ V) U inf_le_left :=
  (RingedSpace.isPullback_restrictInf U V).isoPullback_hom_fst

theorem literalProjectionRight :
    (RingedSpace.isPullback_restrictInf U V).isoPullback.hom ≫
      pullback.snd (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) =
      RingedSpace.restrictMap (U ⊓ V) V inf_le_right :=
  (RingedSpace.isPullback_restrictInf U V).isoPullback_hom_snd

/-- The empty literal intersection is still a full categorical pullback. -/
theorem emptyIntersection :
    IsPullback
      (RingedSpace.restrictMap (⊥ ⊓ U) ⊥ inf_le_left)
      (RingedSpace.restrictMap (⊥ ⊓ U) U inf_le_right)
      (X.ofRestrict (Opens.isOpenEmbedding ⊥)) (X.ofRestrict U.isOpenEmbedding) :=
  RingedSpace.isPullback_restrictInf ⊥ U

variable (C : RingedSpace.OpenCover X) (f : ∀ i, C.obj i ⟶ Y)

/-- A downstream client converts the categorical condition to literal intersections. -/
theorem pullbackToLiteral
    (h : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) :
    ∀ i j, RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i) inf_le_left ≫ f i =
      RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j) inf_le_right ≫ f j :=
  (C.pullback_compatibility_iff_intersection f).mp h

/-- The converse converts literal intersection agreement to categorical compatibility. -/
theorem literalToPullback
    (h : ∀ i j, RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i) inf_le_left ≫ f i =
      RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j) inf_le_right ≫ f j) :
    ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j :=
  (C.pullback_compatibility_iff_intersection f).mpr h

/-- Unique full extension from literal intersection compatibility. -/
theorem uniqueLiteralExtension
    (h : ∀ i j, RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i) inf_le_left ≫ f i =
      RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j) inf_le_right ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, C.ι i ≫ g = f i :=
  C.existsUnique_gluing_of_intersection f h

/-- Vacuous compatibility glues the empty cover of the empty restriction. -/
theorem emptyCoverLiteral (X Y : RingedSpace.{u, u}) :
    ∃! g : X.restrict (Opens.isOpenEmbedding ⊥) ⟶ Y,
      ∀ i : (Test.OpenCover.emptyCover X).J,
        (Test.OpenCover.emptyCover X).ι i ≫ g = i.down.elim := by
  apply (Test.OpenCover.emptyCover X).existsUnique_gluing_of_intersection
    (fun i => i.down.elim)
  intro i
  exact i.down.elim

/-- An infinite indexed cover with empty members still uses literal intersections. -/
theorem infiniteCoverLiteral (X Y : RingedSpace.{u, u})
    (f : ∀ i, (Test.OpenCover.infiniteCover X).obj i ⟶ Y)
    (h : ∀ i j, RingedSpace.restrictMap
      ((Test.OpenCover.infiniteCover X).U i ⊓ (Test.OpenCover.infiniteCover X).U j)
      ((Test.OpenCover.infiniteCover X).U i) inf_le_left ≫ f i =
        RingedSpace.restrictMap
          ((Test.OpenCover.infiniteCover X).U i ⊓ (Test.OpenCover.infiniteCover X).U j)
          ((Test.OpenCover.infiniteCover X).U j) inf_le_right ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, (Test.OpenCover.infiniteCover X).ι i ≫ g = f i :=
  (Test.OpenCover.infiniteCover X).existsUnique_gluing_of_intersection f h

end Test.Restriction
