/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import Test.PresheafInverseImageHom
import all Test.PresheafInverseImageHomConcrete
import Test.PresheafInverseImageHomRoot

/-!
# Compiled-origin axiom census for the inverse-image Hom contribution

Module indices, rather than declaration-name substrings, select every compiled
constant from the focused leaf and its saved clients. This includes private,
generated, and names outside their expected namespaces. The audit rejects any
transitive axiom other than the three permitted foundational axioms.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules : List Name :=
    [`RingedSpaces.Modules.PresheafInverseImageHom,
     `Test.PresheafInverseImageHom,
     `Test.PresheafInverseImageHomConcrete,
     `Test.PresheafInverseImageHomRoot]
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

#print axioms RingedSpaces.Modules.PresheafInverseImage.forward
#print axioms RingedSpaces.Modules.PresheafInverseImage.backward
#print axioms RingedSpaces.Modules.PresheafInverseImage.backward_smul
#print axioms RingedSpaces.Modules.PresheafInverseImage.backward_ι
#print axioms RingedSpaces.Modules.PresheafInverseImage.forward_apply
#print axioms RingedSpaces.Modules.PresheafInverseImage.backward_forward
#print axioms RingedSpaces.Modules.PresheafInverseImage.forward_backward
#print axioms RingedSpaces.Modules.PresheafInverseImage.forward_naturality_left
#print axioms RingedSpaces.Modules.PresheafInverseImage.forward_naturality_right
#print axioms RingedSpaces.Modules.PresheafInverseImage.homEquiv
#print axioms RingedSpaces.Modules.PresheafInverseImage.adjunction
#print axioms RingedSpaces.Modules.PresheafInverseImage.backward_naturality_left
#print axioms RingedSpaces.Modules.PresheafInverseImage.backward_naturality_right
#print axioms RingedSpaces.Modules.PresheafInverseImage.unit_app_eq
#print axioms RingedSpaces.Modules.PresheafInverseImage.unit_apply
#print axioms RingedSpaces.Modules.PresheafInverseImage.counit_app_eq
#print axioms RingedSpaces.Modules.PresheafInverseImage.counit_ι
#print axioms RingedSpaces.Modules.PresheafInverseImage.unit_naturality
#print axioms RingedSpaces.Modules.PresheafInverseImage.counit_naturality
#print axioms RingedSpaces.Modules.PresheafInverseImage.forward_underlying_additive

#print axioms Test.PresheafInverseImageHom.forwardSection
#print axioms Test.PresheafInverseImageHom.descentGenerator
#print axioms Test.PresheafInverseImageHom.descentArbitraryScalar
#print axioms Test.PresheafInverseImageHom.bothHomDirections
#print axioms Test.PresheafInverseImageHom.sourceNaturality
#print axioms Test.PresheafInverseImageHom.targetNaturality
#print axioms Test.PresheafInverseImageHom.actualUnitSection
#print axioms Test.PresheafInverseImageHom.actualCounitGenerator
#print axioms Test.PresheafInverseImageHom.actualUnitCounitNaturalities
#print axioms Test.PresheafInverseImageHom.bothTriangleIdentities
#print axioms Test.PresheafInverseImageHom.ordinaryAdditiveTranspose

#print axioms Test.PresheafInverseImageHomConcrete.genuinelyProperOpenAndNonidentity
#print axioms Test.PresheafInverseImageHomConcrete.nonzeroInputSections
#print axioms Test.PresheafInverseImageHomConcrete.concreteBothDirections
#print axioms Test.PresheafInverseImageHomConcrete.concreteNonzeroForwardSection
#print axioms Test.PresheafInverseImageHomConcrete.properOpenArbitraryCoefficient
#print axioms Test.PresheafInverseImageHomConcrete.properOpenRestrictionNaturality
#print axioms Test.PresheafInverseImageHomConcrete.properOpenCounit
#print axioms Test.PresheafInverseImageHomConcrete.nonzeroUnitSection
#print axioms Test.PresheafInverseImageHomConcrete.concreteMapsAndTriangles
#print axioms Test.PresheafInverseImageHomConcrete.concreteRightTriangle
#print axioms Test.PresheafInverseImageHomConcrete.concreteAdditiveTranspose
#print axioms Test.PresheafInverseImageHomConcrete.emptySourceHomEquiv
#print axioms Test.PresheafInverseImageHomConcrete.zeroRingHomEquiv

#print axioms Test.PresheafInverseImageHomRoot.completeHomEquivalence
#print axioms Test.PresheafInverseImageHomRoot.actualAdjunction
#print axioms Test.PresheafInverseImageHomRoot.additiveComparison

#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwise_jointly_surjective
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwise_smul_ι
#print axioms RingedSpaces.Modules.PresheafInverseImage.ring_map_ι
#print axioms RingedSpaces.Modules.PresheafInverseImage.unit_smul
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_unit
#print axioms RingedSpaces.Modules.PresheafInverseImage.underlyingComparison
#print axioms PresheafOfModules.homMk
#print axioms PresheafOfModules.toPresheaf
#print axioms PresheafOfModules.ModuleColimit.jointly_surjective₂
#print axioms PresheafOfModules.ModuleColimit.smul_eq
#print axioms PresheafOfModules.pushforward
#print axioms PresheafOfModules.pushforwardCompToPresheaf
#print axioms CategoryTheory.Functor.Final.colimitIso
#print axioms CategoryTheory.Functor.pointwiseLeftKanExtension_map
#print axioms CategoryTheory.Functor.pointwiseLeftKanExtensionUnit
#print axioms CategoryTheory.Functor.pointwiseLeftKanExtension_desc_app
#print axioms CategoryTheory.Functor.descOfIsLeftKanExtension_fac
#print axioms CategoryTheory.Adjunction.mkOfHomEquiv
#print axioms TopCat.Presheaf.pullbackPushforwardAdjunction
