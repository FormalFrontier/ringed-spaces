/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import all RingedSpaces.Modules.SheafInverseImage
import all RingedSpaces.Modules.SheafInverseImageHom
import all Test.SheafInverseImage
import all Test.SheafInverseImageConcrete
import all Test.SheafInverseImageRootCoexist

/-!
# Full compiled-origin axiom audit for the new sheaf inverse-image leaves

Module indices select all actual kernel declarations including private and
generated stored bodies, independent of names and namespaces. This is an
isolated import-all audit driver, not a library dependency or ordinary client.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules : List Name :=
    [`RingedSpaces.Modules.SheafInverseImage,
     `RingedSpaces.Modules.SheafInverseImageHom,
     `Test.SheafInverseImage,
     `Test.SheafInverseImageConcrete,
     `Test.SheafInverseImageRootCoexist]
  let mut total : Nat := 0
  let mut empty : Nat := 0
  let mut extra : Nat := 0
  for moduleName in modules do
    let some index := env.getModuleIdx? moduleName
      | throwError "missing compiled module: {moduleName}"
    let names := env.constants.toList.map Prod.fst |>.filter fun name =>
      env.getModuleIdxFor? name == some index
    if names.isEmpty then
      throwError "no compiled declarations from {moduleName}"
    logInfo m!"MODULE {moduleName}: compiled={names.length}"
    for name in names.toArray.qsort (fun first second => first.toString < second.toString) do
      let axioms ← Lean.collectAxioms name
      if axioms.any (fun foundAxiom => foundAxiom != `propext &&
          foundAxiom != `Classical.choice && foundAxiom != `Quot.sound) then
        throwError "unapproved axiom in {moduleName}::{name}: {axioms}"
      if axioms.isEmpty then
        empty := empty + 1
      total := total + 1
      logInfo m!"CENSUS {moduleName}::{name}: {axioms.toList}"
    let additionalNames := env.header.moduleData[index.toNat]!.extraConstNames
    for name in additionalNames do
      if (env.find? name).isSome then
        throwError "unlisted kernel constant in extra IR names: {moduleName}::{name}"
      extra := extra + 1
      logInfo m!"EXTRA_IR_ORIGIN {moduleName}::{name}"
  logInfo m!"SUMMARY compiled={total} noAxioms={empty} allowedOnly={total - empty} extraIR={extra}"

#print axioms RingedSpaces.Modules.PresheafInverseImage.commRingPointwiseComparison
#print axioms RingedSpaces.Modules.PresheafInverseImage.commRingPullbackComparison
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafRing
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafModule
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafUnderlying
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafRingComparison
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafUnderlyingOfSheaf
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageModuleOverActualRing
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageModuleOverActualRingUnderlying
#print axioms RingedSpaces.Modules.SheafInverseImage.sheafForget
#print axioms RingedSpaces.Modules.SheafInverseImage.chosenUnitFac
#print axioms RingedSpaces.Modules.SheafInverseImage.constructedUnitFac
#print axioms RingedSpaces.Modules.SheafInverseImage.pointwiseToPullbackFac
#print axioms RingedSpaces.Modules.SheafInverseImage.presheafComparisonFacApp
#print axioms RingedSpaces.Modules.SheafInverseImage.presheafComparisonFac
#print axioms RingedSpaces.Modules.SheafInverseImage.constructedComparison
#print axioms RingedSpaces.Modules.SheafInverseImage.comparison
#print axioms RingedSpaces.Modules.SheafInverseImage.constructedComparison_sheafUnit
#print axioms RingedSpaces.Modules.SheafInverseImage.constructedComparison_unit
#print axioms RingedSpaces.Modules.SheafInverseImage.pushforwardForget_map
#print axioms RingedSpaces.Modules.SheafInverseImage.comparison_unit
#print axioms RingedSpaces.Modules.SheafInverseImage.comparison_unit_inv
#print axioms RingedSpaces.Modules.SheafInverseImage.comparison_naturality
#print axioms RingedSpaces.Modules.SheafInverseImage.comparisonNatIso
#print axioms RingedSpaces.Modules.SheafInverseImage.comparison_unit_app
#print axioms RingedSpaces.Modules.SheafInverseImage.module
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleUnderlying
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleUnit
#print axioms RingedSpaces.Modules.SheafInverseImage.pointwiseSheafUnit
#print axioms RingedSpaces.Modules.SheafInverseImage.pointwiseSheafUnit_fac
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleUnderlying_inv_eq
#print axioms RingedSpaces.Modules.SheafInverseImage.ringComparison_inv_eq
#print axioms RingedSpaces.Modules.SheafInverseImage.ringUnit_pointwise
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleTargetInstance
#print axioms RingedSpaces.Modules.SheafInverseImage.transportedAction
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleUnit_pointwise
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleUnit_smul
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleFunctor
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleFunctor_obj
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleUnderlyingNatIso

#print axioms RingedSpaces.Modules.SheafInverseImage.sourceRing
#print axioms RingedSpaces.Modules.SheafInverseImage.targetRing
#print axioms RingedSpaces.Modules.SheafInverseImage.pointwiseRing
#print axioms RingedSpaces.Modules.SheafInverseImage.sheafifiedRing
#print axioms RingedSpaces.Modules.SheafInverseImage.moduleSheafCategory
#print axioms RingedSpaces.Modules.SheafInverseImage.ringIso
#print axioms RingedSpaces.Modules.SheafInverseImage.actualUnit
#print axioms RingedSpaces.Modules.SheafInverseImage.ringUnit_full
#print axioms RingedSpaces.Modules.SheafInverseImage.ringUnit_iso
#print axioms RingedSpaces.Modules.SheafInverseImage.ringUnit_inverse
#print axioms RingedSpaces.Modules.SheafInverseImage.ringIso_hom_inv_apply
#print axioms RingedSpaces.Modules.SheafInverseImage.ringIso_inv_hom_apply
#print axioms RingedSpaces.Modules.SheafInverseImage.targetTransport
#print axioms RingedSpaces.Modules.SheafInverseImage.transportForward
#print axioms RingedSpaces.Modules.SheafInverseImage.transportBackward
#print axioms RingedSpaces.Modules.SheafInverseImage.transport_backward_forward
#print axioms RingedSpaces.Modules.SheafInverseImage.transport_forward_backward
#print axioms RingedSpaces.Modules.SheafInverseImage.transportHomEquiv
#print axioms RingedSpaces.Modules.SheafInverseImage.transport_naturality_left
#print axioms RingedSpaces.Modules.SheafInverseImage.transport_naturality_right
#print axioms RingedSpaces.Modules.SheafInverseImage.pushforwardFunctor
#print axioms RingedSpaces.Modules.SheafInverseImage.coefficientSheafUnit
#print axioms RingedSpaces.Modules.SheafInverseImage.presheafTarget
#print axioms RingedSpaces.Modules.SheafInverseImage.ringUnit_inverse_apply
#print axioms RingedSpaces.Modules.SheafInverseImage.nativePushedTarget
#print axioms RingedSpaces.Modules.SheafInverseImage.targetMap
#print axioms RingedSpaces.Modules.SheafInverseImage.targetMapInv
#print axioms RingedSpaces.Modules.SheafInverseImage.targetIso
#print axioms RingedSpaces.Modules.SheafInverseImage.postcomposeIso
#print axioms RingedSpaces.Modules.SheafInverseImage.homEquiv
#print axioms RingedSpaces.Modules.SheafInverseImage.forward_apply
#print axioms RingedSpaces.Modules.SheafInverseImage.homEquiv_naturality_right
#print axioms RingedSpaces.Modules.SheafInverseImage.additiveUnit_naturality
#print axioms RingedSpaces.Modules.SheafInverseImage.additiveUnit_naturality_apply
#print axioms RingedSpaces.Modules.SheafInverseImage.homEquiv_naturality_left
#print axioms RingedSpaces.Modules.SheafInverseImage.forward
#print axioms RingedSpaces.Modules.SheafInverseImage.backward
#print axioms RingedSpaces.Modules.SheafInverseImage.backward_forward
#print axioms RingedSpaces.Modules.SheafInverseImage.forward_backward
#print axioms RingedSpaces.Modules.SheafInverseImage.homEquivCore
#print axioms RingedSpaces.Modules.SheafInverseImage.adjunction
#print axioms RingedSpaces.Modules.SheafInverseImage.unit_app_eq
#print axioms RingedSpaces.Modules.SheafInverseImage.counit_app_eq
#print axioms RingedSpaces.Modules.SheafInverseImage.left_triangle
#print axioms RingedSpaces.Modules.SheafInverseImage.right_triangle
#print axioms RingedSpaces.Modules.SheafInverseImage.forward_underlying
#print axioms RingedSpaces.Modules.SheafInverseImage.forward_underlying_additive
#print axioms RingedSpaces.Modules.SheafInverseImage.unit_underlying
#print axioms RingedSpaces.Modules.SheafInverseImage.backward_underlying_additive

#print axioms Test.SheafInverseImage.functorMaps
#print axioms Test.SheafInverseImage.comparisonNatural
#print axioms Test.SheafInverseImage.fullRingUnit
#print axioms Test.SheafInverseImage.underlyingNatural
#print axioms Test.SheafInverseImage.bothDirections
#print axioms Test.SheafInverseImage.sourceNaturality
#print axioms Test.SheafInverseImage.targetNaturality
#print axioms Test.SheafInverseImage.unitAndCounit
#print axioms Test.SheafInverseImage.bothTriangles
#print axioms Test.SheafInverseImage.wholeAdditiveUnit
#print axioms Test.SheafInverseImage.wholeAdditiveTranspose

#print axioms Test.SheafInverseImageConcrete.properAndNonidentity
#print axioms Test.SheafInverseImageConcrete.properOpenRingUnit
#print axioms Test.SheafInverseImageConcrete.emptyOpenRingUnit
#print axioms Test.SheafInverseImageConcrete.properOpenAdditiveUnit
#print axioms Test.SheafInverseImageConcrete.nonidentityAdjunction
#print axioms Test.SheafInverseImageConcrete.emptySpaceAdjunction
#print axioms Test.SheafInverseImageConcrete.zeroRingBoundary

#print axioms Test.SheafInverseImageRootCoexist.wholeUnitWithOldRoot
