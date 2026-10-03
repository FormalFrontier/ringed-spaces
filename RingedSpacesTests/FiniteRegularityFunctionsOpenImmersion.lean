/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Open-interval clients for finite-regularity scalar-function restriction. -/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace FiniteRegularityFunctionsOpenImmersionTest

open FiniteRegularityFunctions

/-- A proper real open interval with its induced charts. -/
def interval : Opens ℝ := ⟨Set.Ioo (-1) 1, isOpen_Ioo⟩

private def smallerInterval : Opens ℝ := ⟨Set.Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩

private def origin : interval := ⟨0, by norm_num [interval]⟩

private theorem origin_mem_smallerInterval : (origin : ℝ) ∈ smallerInterval := by
  norm_num [origin, smallerInterval]

private theorem smaller_le_interval : smallerInterval ≤ interval := by
  intro point hpoint
  change -(1 / 2 : ℝ) < point ∧ point < (1 / 2 : ℝ) at hpoint
  change (-1 : ℝ) < point ∧ point < 1
  constructor <;> linarith [hpoint.1, hpoint.2]

example : (origin : ℝ) ∈ interval ∧ (2 : ℝ) ∉ interval ∧
    smallerInterval ≤ interval := by
  constructor
  · exact origin.2
  constructor
  · norm_num [interval]
  · exact smaller_le_interval

private theorem inclusionContMDiff (r : ℕ) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) (r : ℕ∞ω) (Subtype.val : interval → ℝ) :=
  contMDiff_subtype_val

private def coordinate : (sheaf 𝓘(ℝ) ℝ 1).presheaf.obj (op (⊤ : Opens ℝ)) :=
  ofFunction (IM := 𝓘(ℝ)) (M := ℝ) 1 ⊤
    (fun point => (point : ℝ) + 2) (contMDiff_subtype_val.add contMDiff_const)

private def preimageOrigin :
    ContinuousFunctions.inverseImage interval ℝ (Subtype.val : interval → ℝ)
      (inclusionContMDiff 1).continuous ⊤ :=
  ⟨origin, by change (origin : ℝ) ∈ (⊤ : Opens ℝ); trivial⟩

private def preimageOriginSmall :
    ContinuousFunctions.inverseImage interval ℝ (Subtype.val : interval → ℝ)
      (inclusionContMDiff 1).continuous smallerInterval :=
  ⟨origin, origin_mem_smallerInterval⟩

example :
    ((restrictLocallyRingedSpaceIso 𝓘(ℝ) ℝ 1 interval).inv ≫
      (locallyRingedSpace 1 𝓘(ℝ) ℝ).ofRestrict interval.isOpenEmbedding).base =
    TopCat.ofHom ⟨(Subtype.val : interval → ℝ), continuous_subtype_val⟩ := by
  rw [restrictLocallyRingedSpaceIso_inv_ofRestrict]
  exact locallyRingedSpaceMap_base 𝓘(ℝ) 𝓘(ℝ) interval ℝ 1
    Subtype.val (inclusionContMDiff 1)

example : precompose 𝓘(ℝ) 𝓘(ℝ) interval ℝ 1 Subtype.val
    (inclusionContMDiff 1) ⊤ coordinate preimageOrigin = 2 := by
  rw [precompose_apply]
  norm_num [coordinate, preimageOrigin, origin, ofFunction]

example : precompose 𝓘(ℝ) 𝓘(ℝ) interval ℝ 1 Subtype.val
    (inclusionContMDiff 1) smallerInterval
    (restrict (IM := 𝓘(ℝ)) (M := ℝ) 1 smaller_le_interval
      (restrict (IM := 𝓘(ℝ)) (M := ℝ) 1
        (le_top : interval ≤ (⊤ : Opens ℝ)) coordinate))
    preimageOriginSmall = 2 := by
  rw [precompose_apply, restrict_apply, restrict_apply]
  norm_num [coordinate, preimageOriginSmall, origin, ofFunction]

private theorem coordinate_germ_eval : eval 𝓘(ℝ) interval 1 origin
    ((locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) interval ℝ 1 Subtype.val
      (inclusionContMDiff 1)).stalkMap origin
      ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ ⊤ (origin : ℝ) (by simp) coordinate)) = 2 := by
  have hmem : origin ∈ ContinuousFunctions.inverseImage interval ℝ Subtype.val
      (inclusionContMDiff 1).continuous ⊤ := preimageOrigin.2
  rw [stalkMap_germ 𝓘(ℝ) 𝓘(ℝ) interval ℝ 1 Subtype.val
    (inclusionContMDiff 1) (⊤ : Opens ℝ) origin (by simp) coordinate]
  change eval 𝓘(ℝ) interval 1 origin
    ((sheaf 𝓘(ℝ) interval 1).presheaf.germ
      (ContinuousFunctions.inverseImage interval ℝ Subtype.val
        (inclusionContMDiff 1).continuous ⊤) origin hmem
      (precompose 𝓘(ℝ) 𝓘(ℝ) interval ℝ 1 Subtype.val
        (inclusionContMDiff 1) ⊤ coordinate)) = 2
  rw [eval_germ (IM := 𝓘(ℝ)) (M := interval) 1
    (ContinuousFunctions.inverseImage interval ℝ Subtype.val
      (inclusionContMDiff 1).continuous ⊤) origin hmem, precompose_apply]
  norm_num [coordinate, origin, ofFunction]

example : eval 𝓘(ℝ) interval 1 origin
    (((restrictLocallyRingedSpaceIso 𝓘(ℝ) ℝ 1 interval).inv ≫
      (locallyRingedSpace 1 𝓘(ℝ) ℝ).ofRestrict interval.isOpenEmbedding).stalkMap origin
      ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ ⊤
        (((restrictLocallyRingedSpaceIso 𝓘(ℝ) ℝ 1 interval).inv ≫
          (locallyRingedSpace 1 𝓘(ℝ) ℝ).ofRestrict interval.isOpenEmbedding).base origin)
        (by simp) coordinate)) = 2 := by
  let value : (locallyRingedSpace 1 𝓘(ℝ) interval ⟶
      locallyRingedSpace 1 𝓘(ℝ) ℝ) → ℝ := fun morphism =>
    eval 𝓘(ℝ) interval 1 origin
      (morphism.stalkMap origin
        ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ ⊤ (morphism.base origin)
          (by simp) coordinate))
  change value ((restrictLocallyRingedSpaceIso 𝓘(ℝ) ℝ 1 interval).inv ≫
    (locallyRingedSpace 1 𝓘(ℝ) ℝ).ofRestrict interval.isOpenEmbedding) = 2
  calc
    _ = value (locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) interval ℝ 1 Subtype.val
          (inclusionContMDiff 1)) :=
      congrArg value (restrictLocallyRingedSpaceIso_inv_ofRestrict
        𝓘(ℝ) ℝ 1 interval)
    _ = 2 := by
      change eval 𝓘(ℝ) interval 1 origin
        ((locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) interval ℝ 1 Subtype.val
          (inclusionContMDiff 1)).stalkMap origin
          ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ ⊤ (origin : ℝ) (by simp) coordinate)) = 2
      exact coordinate_germ_eval

private def zeroCoordinate : (sheaf 𝓘(ℝ) ℝ 0).presheaf.obj (op (⊤ : Opens ℝ)) :=
  ofFunction (IM := 𝓘(ℝ)) (M := ℝ) 0 ⊤ (fun point => |(point : ℝ)|)
    (contMDiff_zero_iff.mpr (continuous_abs.comp continuous_subtype_val))

example : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := not_differentiableAt_abs_zero

example : zeroToContinuous (IM := 𝓘(ℝ)) (M := interval)
    (ContinuousFunctions.inverseImage interval ℝ Subtype.val
      (inclusionContMDiff 0).continuous ⊤)
    (precompose 𝓘(ℝ) 𝓘(ℝ) interval ℝ 0 Subtype.val
      (inclusionContMDiff 0) ⊤ zeroCoordinate) preimageOrigin = 0 := by
  rw [zeroToContinuous_apply, precompose_apply]
  norm_num [zeroCoordinate, origin, preimageOrigin, ofFunction]
  rfl

example : LocallyRingedSpace.IsOpenImmersion
    (locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) (⊥ : Opens ℝ) ℝ 1
      Subtype.val contMDiff_subtype_val) := by
  infer_instance

end FiniteRegularityFunctionsOpenImmersionTest
