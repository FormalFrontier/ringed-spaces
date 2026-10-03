/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import all RingedSpaces.Modules.RingedSpacePullback
import all RingedSpacesTests.RingedSpacePullback
import all RingedSpacesTests.RingedSpacePullbackConcrete
import all RingedSpacesTests.RingedSpacePullbackRootCoexist

set_option warningAsError true

/-!
# Pinned compiled-origin axiom census for the explicit pullback

The census examines every compiled constant originating in each newly added
library or client module, including generated or private constants. Import
dependencies are checked transitively rather than counted a second time.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules : List Name :=
    [`RingedSpaces.Modules.RingedSpacePullback,
     `RingedSpacesTests.RingedSpacePullback,
     `RingedSpacesTests.RingedSpacePullbackConcrete,
     `RingedSpacesTests.RingedSpacePullbackRootCoexist]
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

#print axioms RingedSpaces.Modules.RingedSpacePullback.inverseRing
#print axioms RingedSpaces.Modules.RingedSpacePullback.coefficientMap
#print axioms RingedSpaces.Modules.RingedSpacePullback.pullbackFunctor
#print axioms RingedSpaces.Modules.RingedSpacePullback.tensorComparison
#print axioms RingedSpaces.Modules.RingedSpacePullback.coefficientMap_ringSheafMap
#print axioms RingedSpaces.Modules.RingedSpacePullback.adjunction
#print axioms RingedSpaces.Modules.RingedSpacePullback.homEquiv
#print axioms RingedSpaces.Modules.RingedSpacePullback.homEquiv_apply
#print axioms RingedSpaces.Modules.RingedSpacePullback.homEquiv_inverse_laws
#print axioms RingedSpaces.Modules.RingedSpacePullback.homEquiv_naturality_left
#print axioms RingedSpaces.Modules.RingedSpacePullback.homEquiv_naturality_right
#print axioms RingedSpaces.Modules.RingedSpacePullback.unit_formula
#print axioms RingedSpaces.Modules.RingedSpacePullback.triangle_identities
#print axioms RingedSpaces.Modules.RingedSpacePullback.fullPushforwardIsRightAdjoint
#print axioms RingedSpaces.Modules.RingedSpacePullback.nativeAdjunction
#print axioms RingedSpaces.Modules.RingedSpacePullback.nativeComparison
#print axioms RingedSpaces.Modules.RingedSpacePullback.nativeComparison_unit
#print axioms RingedSpaces.Modules.RingedSpacePullback.nativeComparison_counit
#print axioms RingedSpaces.Modules.RingedSpacePullback.nativeComparison_homEquiv

#print axioms RingedSpaces.Modules.SheafInverseImage.adjunction
#print axioms RingedSpaces.Modules.tensorSheafAdjunction
#print axioms RingedSpaces.Modules.opensRightSheafNatIso
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso
#print axioms SheafOfModules.pullbackPushforwardAdjunction
#print axioms CategoryTheory.Adjunction.leftAdjointUniq

#print axioms Test.RingedSpacePullback.fullAdjunction
#print axioms Test.RingedSpacePullback.leftInverse
#print axioms Test.RingedSpacePullback.rightInverse
#print axioms Test.RingedSpacePullback.sourceNatural
#print axioms Test.RingedSpacePullback.targetNatural
#print axioms Test.RingedSpacePullback.fullUnit
#print axioms Test.RingedSpacePullback.nativeUnit
#print axioms Test.RingedSpacePullback.nativeTransposes
#print axioms Test.RingedSpacePullback.bothTriangles
#print axioms Test.RingedSpacePullbackConcrete.properAndNonidentity
#print axioms Test.RingedSpacePullbackConcrete.properOpenFullStructure
#print axioms Test.RingedSpacePullbackConcrete.nonidentityComparison
#print axioms Test.RingedSpacePullbackConcrete.properOpenUnit
#print axioms Test.RingedSpacePullbackConcrete.emptyComparison
#print axioms Test.RingedSpacePullbackConcrete.zeroRingAdjunction
#print axioms Test.RingedSpacePullbackRootCoexist.comparison

#lint
