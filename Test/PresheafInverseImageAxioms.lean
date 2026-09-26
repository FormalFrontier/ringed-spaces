/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import Test.PresheafInverseImage
import all Test.PresheafInverseImageConcrete
import Test.PresheafInverseImageRoot

/-!
# Transitive axiom audit for inverse-image module presheaves

The environment census includes private and generated declarations. The same
`Lean.collectAxioms` mechanism powers `#print axioms`; explicit prints pin the
public API, all saved clients and selected native dependencies. Enumerating
generated declarations avoids unstable `_proof_` references in source text.
-/

open Lean Elab Command

run_cmd do
  let names := (← getEnv).constants.toList.map Prod.fst |>.filter fun name =>
    (name.toString.splitOn "RingedSpaces.Modules.PresheafInverseImage").length > 1 ||
      (name.toString.splitOn "Test.PresheafInverseImage").length > 1
  let mut noAxioms : Nat := 0
  let mut allowedOnly : Nat := 0
  for name in names.toArray.qsort (fun first second => first.toString < second.toString) do
    let axioms ← Lean.collectAxioms name
    if axioms.any (fun foundAxiom => foundAxiom != `propext &&
        foundAxiom != `Classical.choice && foundAxiom != `Quot.sound) then
      throwError "unapproved axiom in {name}: {axioms}"
    if axioms.isEmpty then
      noAxioms := noAxioms + 1
    else
      allowedOnly := allowedOnly + 1
    logInfo m!"CENSUS {name} : {axioms.toList}"
  logInfo m!"SUMMARY census={names.length} empty={noAxioms} allowedOnly={allowedOnly}"

#print axioms RingedSpaces.Modules.PresheafInverseImage.index
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseModule
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwise_smul_ι
#print axioms RingedSpaces.Modules.PresheafInverseImage.ring_map_ι
#print axioms RingedSpaces.Modules.PresheafInverseImage.group_map_ι
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwise_jointly_surjective
#print axioms RingedSpaces.Modules.PresheafInverseImage.restriction_smul
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageModule
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseToPullback
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseMap
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_ι
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_smul
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageMap
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_id
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_comp
#print axioms RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_unit
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseToPullback_fac
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul
#print axioms RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul_eq
#print axioms RingedSpaces.Modules.PresheafInverseImage.unit_smul
#print axioms RingedSpaces.Modules.PresheafInverseImage.underlyingComparison

#print axioms Test.PresheafInverseImage.simultaneousGenerators
#print axioms Test.PresheafInverseImage.generatorAction
#print axioms Test.PresheafInverseImage.ringRestrictionGenerator
#print axioms Test.PresheafInverseImage.moduleRestrictionGenerator
#print axioms Test.PresheafInverseImage.restrictionArbitraryScalar
#print axioms Test.PresheafInverseImage.restrictionIdentityComposition
#print axioms Test.PresheafInverseImage.inducedMapGenerator
#print axioms Test.PresheafInverseImage.inducedMapArbitraryScalar
#print axioms Test.PresheafInverseImage.inducedMapNaturality
#print axioms Test.PresheafInverseImage.inducedFunctorLaws
#print axioms Test.PresheafInverseImage.actualUnitAction
#print axioms Test.PresheafInverseImage.actualUnitNaturality
#print axioms Test.PresheafInverseImage.additiveComparisonNatural
#print axioms Test.PresheafInverseImage.additiveComparisonUnit

#print axioms Test.PresheafInverseImageConcrete.genuinelyProperNonempty
#print axioms Test.PresheafInverseImageConcrete.nonidentityNonzeroInputs
#print axioms Test.PresheafInverseImageConcrete.nonidentityGenerator
#print axioms Test.PresheafInverseImageConcrete.nonzeroInputGenerator
#print axioms Test.PresheafInverseImageConcrete.properOpenArbitraryScalar
#print axioms Test.PresheafInverseImageConcrete.emptySourceUnit
#print axioms Test.PresheafInverseImageConcrete.emptyOpenRestriction
#print axioms Test.PresheafInverseImageConcrete.zeroRingIsTrivial
#print axioms Test.PresheafInverseImageConcrete.zeroRingAction

#print axioms Test.PresheafInverseImageRoot.arbitraryScalarRestriction
#print axioms Test.PresheafInverseImageRoot.actualUnit
#print axioms Test.PresheafInverseImageRoot.fullUnderlyingIso
#print axioms Test.PresheafInverseImageRoot.additiveUnitComparison

#print axioms PresheafOfModules.ModuleColimit.instModuleCarrierPtOppositeRingCat
#print axioms PresheafOfModules.ModuleColimit.smul_eq
#print axioms PresheafOfModules.ModuleColimit.jointly_surjective₂
#print axioms CategoryTheory.Functor.Final.colimitIso
#print axioms CategoryTheory.Functor.pointwiseLeftKanExtension_map
#print axioms CategoryTheory.Functor.pointwiseLeftKanExtensionUnit
#print axioms CategoryTheory.Functor.leftKanExtensionUnique
#print axioms PresheafOfModules.ofPresheaf
#print axioms PresheafOfModules.homMk
#print axioms TopCat.Presheaf.pullback
