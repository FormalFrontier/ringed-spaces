/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import Test.OpenCover
import Test.Restriction
import Test.Root
import Test.InverseImage

/-!
# Public and downstream-client axiom audit

Each command reports the transitive axioms of a proof-bearing public declaration or client.
-/

#print axioms AlgebraicGeometry.RingedSpace.OpenCover.ι_glueMorphisms
#print axioms AlgebraicGeometry.RingedSpace.OpenCover.hom_ext
#print axioms AlgebraicGeometry.RingedSpace.OpenCover.existsUnique_gluing
#print axioms Test.OpenCover.arbitraryFamily
#print axioms Test.OpenCover.emptyFamily
#print axioms Test.OpenCover.infiniteFamily
#print axioms Test.Root.gluing
#print axioms AlgebraicGeometry.RingedSpace.restrictMap
#print axioms AlgebraicGeometry.RingedSpace.restrictMap_ofRestrict
#print axioms AlgebraicGeometry.RingedSpace.restrictMap_ofRestrict_assoc
#print axioms AlgebraicGeometry.RingedSpace.restrictMap_base
#print axioms AlgebraicGeometry.RingedSpace.restrictMap_comp
#print axioms AlgebraicGeometry.RingedSpace.restrictMap_comp_assoc
#print axioms AlgebraicGeometry.RingedSpace.restrictMap_id
#print axioms AlgebraicGeometry.RingedSpace.isPullback_restrictInf
#print axioms AlgebraicGeometry.RingedSpace.OpenCover.pullback_compatibility_iff_intersection
#print axioms AlgebraicGeometry.RingedSpace.OpenCover.existsUnique_gluing_of_intersection
#print axioms Test.Restriction.literalInclusion
#print axioms Test.Restriction.identityRestriction
#print axioms Test.Restriction.composedRestriction
#print axioms Test.Restriction.fullFactorization
#print axioms Test.Restriction.sheafComponent
#print axioms Test.Restriction.literalPullback
#print axioms Test.Restriction.literalProjectionLeft
#print axioms Test.Restriction.literalProjectionRight
#print axioms Test.Restriction.emptyIntersection
#print axioms Test.Restriction.pullbackToLiteral
#print axioms Test.Restriction.literalToPullback
#print axioms Test.Restriction.uniqueLiteralExtension
#print axioms Test.Restriction.emptyCoverLiteral
#print axioms Test.Restriction.infiniteCoverLiteral
#print axioms Test.Root.literalGluing
#print axioms AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac
#print axioms AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift
#print axioms AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_uniq
#print axioms CategoryTheory.IsPullback.isoPullback_hom_fst
#print axioms CategoryTheory.IsPullback.isoPullback_hom_snd
#print axioms CategoryTheory.IsPullback.isoPullback
#print axioms CategoryTheory.Limits.Multicoequalizer.π_desc
#print axioms CategoryTheory.Limits.Multicoequalizer.hom_ext
#print axioms CategoryTheory.GlueData.ι_jointly_surjective
#print axioms AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso
#print axioms AlgebraicGeometry.SheafedSpace.IsOpenImmersion.to_iso
#print axioms AlgebraicGeometry.RingedSpace.inverseImage
#print axioms AlgebraicGeometry.RingedSpace.inverseImage_carrier
#print axioms AlgebraicGeometry.RingedSpace.inverseImage_sheaf
#print axioms AlgebraicGeometry.RingedSpace.ofInverseImage
#print axioms AlgebraicGeometry.RingedSpace.ofInverseImage_base
#print axioms AlgebraicGeometry.RingedSpace.ofInverseImage_c
#print axioms AlgebraicGeometry.RingedSpace.ofInverseImage_c_app
#print axioms AlgebraicGeometry.RingedSpace.inverseImageMap
#print axioms AlgebraicGeometry.RingedSpace.inverseImageMap_unit
#print axioms AlgebraicGeometry.RingedSpace.inverseImageMap_unit_hom
#print axioms AlgebraicGeometry.RingedSpace.inverseImageMap_unit_app
#print axioms AlgebraicGeometry.RingedSpace.inverseImageMap_unit_components
#print axioms AlgebraicGeometry.RingedSpace.toInverseImage
#print axioms AlgebraicGeometry.RingedSpace.toInverseImage_base
#print axioms AlgebraicGeometry.RingedSpace.toInverseImage_c
#print axioms AlgebraicGeometry.RingedSpace.toInverseImage_c_app
#print axioms AlgebraicGeometry.RingedSpace.toInverseImage_c_app_eq
#print axioms AlgebraicGeometry.RingedSpace.toInverseImage_ofInverseImage
#print axioms Test.InverseImage.arbitraryContinuous
#print axioms Test.InverseImage.unitOnOpen
#print axioms Test.InverseImage.arbitraryFull
#print axioms Test.InverseImage.componentOnOpen
#print axioms Test.InverseImage.sectionMaps
#print axioms Test.InverseImage.identity
#print axioms Test.InverseImage.emptyCarrier
#print axioms Test.InverseImage.zeroRingSpace
#print axioms Test.InverseImage.zeroRing
#print axioms Test.InverseImage.nonidentityFull
#print axioms Test.Root.inverseImageFull
#print axioms Test.Root.inverseImageContinuous
#print axioms Test.Root.inverseImageSections
