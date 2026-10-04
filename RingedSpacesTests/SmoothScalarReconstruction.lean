/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Scalar-preserving smooth morphisms on proper open domains

A triangular polynomial self-map of a two-dimensional coordinate slab is
nonlinear and nonidentity. Its induced full morphism preserves constants and
pulls back nonconstant sections on nested opens by precomposition, over both
the real and complex fields. Zero-dimensional and empty domains exercise the
boundary cases of the same scalar-preservation API.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace SmoothScalarReconstructionTest

private abbrev Plane (𝕜 : Type*) := Fin 2 → 𝕜

private def slab (𝕜 : Type*) [NontriviallyNormedField 𝕜] : Opens (Plane 𝕜) :=
  ⟨(fun point : Plane 𝕜 => point 0) ⁻¹' Metric.ball 0 1,
    Metric.isOpen_ball.preimage (continuous_apply 0)⟩

private def triangular {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (point : slab 𝕜) : slab 𝕜 :=
  ⟨fun index => if index = 0 then point.1 0
    else point.1 1 + point.1 0 * point.1 0, by
      exact point.2⟩

private theorem triangular_smooth {𝕜 : Type*} [NontriviallyNormedField 𝕜] :
    ContMDiff 𝓘(𝕜, Plane 𝕜) 𝓘(𝕜, Plane 𝕜) ∞ (triangular (𝕜 := 𝕜)) := by
  have hcoord (index : Fin 2) : ContMDiff 𝓘(𝕜, Plane 𝕜) 𝓘(𝕜) ∞
      (fun point : slab 𝕜 => point.1 index) := by
    simpa only [ContinuousLinearMap.proj_apply, Function.comp_def] using
      (show Plane 𝕜 →L[𝕜] 𝕜 from ContinuousLinearMap.proj index).contMDiff.comp
        contMDiff_subtype_val
  have hraw : ContMDiff 𝓘(𝕜, Plane 𝕜) 𝓘(𝕜, Plane 𝕜) ∞
      (fun point : slab 𝕜 => (triangular point : Plane 𝕜)) := by
    apply contMDiff_pi_space.2
    intro index
    fin_cases index
    · simpa [triangular] using hcoord 0
    · convert (hcoord 1).add ((hcoord 0).mul (hcoord 0)) using 1
      funext point
      simp [triangular, Pi.add_apply, Pi.mul_apply]
  exact (ContMDiff.subtypeVal_comp_iff (slab 𝕜) triangular).mp hraw

private theorem triangular_preserves {𝕜 : Type*} [NontriviallyNormedField 𝕜] :
    ChartedSpace.PreservesSmoothScalars 𝓘(𝕜, Plane 𝕜)
      (ChartedSpace.locallyRingedSpaceMap triangular triangular_smooth).toHom :=
  ChartedSpace.preservesSmoothScalars_locallyRingedSpaceMap
    𝓘(𝕜, Plane 𝕜) triangular triangular_smooth

private theorem real_preserves_without_hypothesis :
    ChartedSpace.PreservesSmoothScalars 𝓘(ℝ, Plane ℝ)
      (ChartedSpace.locallyRingedSpaceMap
        (triangular (𝕜 := ℝ)) triangular_smooth).toHom :=
  ChartedSpace.preservesSmoothScalars_real 𝓘(ℝ, Plane ℝ) 𝓘(ℝ, Plane ℝ) _

private def testPoint {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (value : 𝕜) (hvalue : ‖value‖ < 1) : slab 𝕜 :=
  ⟨fun index => if index = 0 then value else 0, by
    simpa [slab, Metric.mem_ball, dist_zero_left] using hvalue⟩

private def inner (𝕜 : Type*) [NontriviallyNormedField 𝕜] : Opens (slab 𝕜) :=
  ⟨{point | ‖point.1 0‖ < (3 / 4 : ℝ)},
    isOpen_lt (((continuous_apply 0).comp continuous_subtype_val).norm) continuous_const⟩

private def secondSection {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (U : Opens (slab 𝕜)) :
    (smoothSheafCommRing 𝓘(𝕜, Plane 𝕜) 𝓘(𝕜) (slab 𝕜) 𝕜).presheaf.obj (op U) := by
  refine ⟨fun point => point.1.1 1, ?_⟩
  change ContMDiff 𝓘(𝕜, Plane 𝕜) 𝓘(𝕜) ∞
    (fun point : U => point.1.1 1)
  simpa only [ContinuousLinearMap.proj_apply, Function.comp_def] using
    (show Plane 𝕜 →L[𝕜] 𝕜 from ContinuousLinearMap.proj (1 : Fin 2)).contMDiff.comp
      (contMDiff_subtype_val.comp contMDiff_subtype_val)

private def sectionPoint {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (value : 𝕜) : inner 𝕜 :=
  ⟨⟨fun index => if index = 0 then 0 else value, by
    simp [slab, Metric.mem_ball]⟩, by
    change ‖(0 : 𝕜)‖ < (3 / 4 : ℝ)
    norm_num⟩

example : (inner ℝ).1.Nonempty :=
  ⟨(sectionPoint (0 : ℝ)).1, (sectionPoint (0 : ℝ)).2⟩

example : inner ℝ ≠ ⊤ := by
  intro h
  have hpoint : testPoint (𝕜 := ℝ) (7 / 8) (by norm_num) ∈ inner ℝ := by
    rw [h]
    trivial
  norm_num [inner, testPoint] at hpoint

example : (secondSection (inner ℝ)).1 (sectionPoint (0 : ℝ)) ≠
    (secondSection (inner ℝ)).1 (sectionPoint (1 : ℝ)) := by
  norm_num [secondSection, sectionPoint]

example :
    (smoothSheafCommRing 𝓘(ℝ, Plane ℝ) 𝓘(ℝ) (slab ℝ) ℝ).presheaf.map
      (homOfLE (show inner ℝ ≤ (⊤ : Opens (slab ℝ)) from le_top)).op
        (secondSection (⊤ : Opens (slab ℝ))) = secondSection (inner ℝ) := by
  apply Subtype.ext
  funext point
  rfl

private theorem testPoint_mem_preimage {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (value : 𝕜) (hvalue : ‖value‖ < (3 / 4 : ℝ)) :
    testPoint value (lt_trans hvalue (by norm_num)) ∈
      (Opens.map (ChartedSpace.locallyRingedSpaceMap triangular triangular_smooth).base).obj
        (inner 𝕜) := by
  change triangular (testPoint value (lt_trans hvalue (by norm_num))) ∈ inner 𝕜
  simpa [triangular, testPoint, inner] using hvalue

private theorem real_open_proper :
    (fun index : Fin 2 => if index = 0 then (2 : ℝ) else 0) ∉ slab ℝ := by
  norm_num [slab, Metric.mem_ball, dist_eq_norm]

private theorem complex_open_proper :
    (fun index : Fin 2 => if index = 0 then (2 : ℂ) else 0) ∉ slab ℂ := by
  norm_num [slab, Metric.mem_ball, dist_eq_norm]

example : triangular (testPoint (𝕜 := ℝ) (1 / 2) (by norm_num)) ≠
    testPoint (𝕜 := ℝ) (1 / 2) (by norm_num) := by
  intro equality
  have atSecond := congrArg (fun point : slab ℝ => point.1 (1 : Fin 2)) equality
  norm_num [triangular, testPoint] at atSecond

example : triangular (testPoint (𝕜 := ℂ) (1 / 2) (by norm_num)) ≠
    testPoint (𝕜 := ℂ) (1 / 2) (by norm_num) := by
  intro equality
  have atSecond := congrArg (fun point : slab ℂ => point.1 (1 : Fin 2)) equality
  norm_num [triangular, testPoint] at atSecond

example :
    (triangular (testPoint (𝕜 := ℝ) (1 / 2) (by norm_num))).1 (1 : Fin 2) ≠
      2 * (triangular (testPoint (𝕜 := ℝ) (1 / 4) (by norm_num))).1 (1 : Fin 2) := by
  norm_num [triangular, testPoint]

example :
    ((ChartedSpace.locallyRingedSpaceMap triangular triangular_smooth).c.app
      (op (inner ℝ)) (secondSection (inner ℝ))).1
        ⟨testPoint (𝕜 := ℝ) (1 / 2) (by norm_num),
          testPoint_mem_preimage (𝕜 := ℝ) (1 / 2) (by norm_num)⟩ =
      (1 / 4 : ℝ) := by
  have heval := real_preserves_without_hypothesis.apply
    𝓘(ℝ, Plane ℝ) (inner ℝ) (secondSection (inner ℝ))
    ⟨testPoint (𝕜 := ℝ) (1 / 2) (by norm_num),
      testPoint_mem_preimage (𝕜 := ℝ) (1 / 2) (by norm_num)⟩
  norm_num [secondSection, triangular, testPoint] at heval ⊢
  exact heval

example :
    HEq (ChartedSpace.locallyRingedSpaceMap
      (triangular (𝕜 := ℝ)) triangular_smooth).toHom.c
    (ChartedSpace.locallyRingedSpaceMap (M := slab ℝ) (N := slab ℝ)
      ((ChartedSpace.locallyRingedSpaceMap triangular triangular_smooth).toHom.base :
        slab ℝ → slab ℝ)
      (triangular_preserves (𝕜 := ℝ)).contMDiff_base).toHom.c :=
  (triangular_preserves (𝕜 := ℝ)).eq_locallyRingedSpaceMap_c

example :
    ((ChartedSpace.locallyRingedSpaceMap triangular triangular_smooth).c.app
      (op (inner ℂ)) (secondSection (inner ℂ))).1
        ⟨testPoint (𝕜 := ℂ) (1 / 2) (by norm_num),
          testPoint_mem_preimage (𝕜 := ℂ) (1 / 2) (by norm_num)⟩ =
      (1 / 4 : ℂ) := by
  have heval := triangular_preserves.apply
    𝓘(ℂ, Plane ℂ) (inner ℂ) (secondSection (inner ℂ))
    ⟨testPoint (𝕜 := ℂ) (1 / 2) (by norm_num),
      testPoint_mem_preimage (𝕜 := ℂ) (1 / 2) (by norm_num)⟩
  norm_num [secondSection, triangular, testPoint] at heval ⊢
  exact heval

example :
    HEq (ChartedSpace.locallyRingedSpaceMap
      (triangular (𝕜 := ℂ)) triangular_smooth).toHom.c
    (ChartedSpace.locallyRingedSpaceMap (M := slab ℂ) (N := slab ℂ)
      ((ChartedSpace.locallyRingedSpaceMap triangular triangular_smooth).toHom.base :
        slab ℂ → slab ℂ)
      (triangular_preserves (𝕜 := ℂ)).contMDiff_base).toHom.c :=
  (triangular_preserves (𝕜 := ℂ)).eq_locallyRingedSpaceMap_c

private abbrev PointModel (𝕜 : Type*) := Fin 0 → 𝕜

private def zeroDomain (𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    Opens (PointModel 𝕜) := ⊤

private theorem zero_preserves {𝕜 : Type*} [NontriviallyNormedField 𝕜] :
    ChartedSpace.PreservesSmoothScalars 𝓘(𝕜, PointModel 𝕜)
      (ChartedSpace.locallyRingedSpaceMap
        (id : zeroDomain 𝕜 → zeroDomain 𝕜) contMDiff_id).toHom :=
  ChartedSpace.preservesSmoothScalars_locallyRingedSpaceMap
    𝓘(𝕜, PointModel 𝕜) _ contMDiff_id

example (a : ℝ) :
    ((ChartedSpace.locallyRingedSpaceMap
      (id : zeroDomain ℝ → zeroDomain ℝ) contMDiff_id).c.app
        (op (⊤ : Opens (zeroDomain ℝ)))
        (ContMDiffMap.C (I := 𝓘(ℝ, PointModel ℝ))
          (N := (⊤ : Opens (zeroDomain ℝ))) (A := ℝ) (n := ∞) a)).1
          ⟨⟨(0 : PointModel ℝ), trivial⟩, trivial⟩ = a :=
  (zero_preserves (𝕜 := ℝ)).const_apply 𝓘(ℝ, PointModel ℝ) a _

private def emptyDomain (𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    Opens (Plane 𝕜) := ⊥

private def emptyMap {𝕜 : Type*} [NontriviallyNormedField 𝕜] :
    emptyDomain 𝕜 → slab 𝕜 := fun point => False.elim point.2

private theorem emptyMap_smooth {𝕜 : Type*} [NontriviallyNormedField 𝕜] :
    ContMDiff 𝓘(𝕜, Plane 𝕜) 𝓘(𝕜, Plane 𝕜) ∞ (emptyMap (𝕜 := 𝕜)) := by
  intro point
  exact False.elim point.2

private theorem empty_preserves {𝕜 : Type*} [NontriviallyNormedField 𝕜] :
    ChartedSpace.PreservesSmoothScalars 𝓘(𝕜, Plane 𝕜)
      (ChartedSpace.locallyRingedSpaceMap emptyMap emptyMap_smooth).toHom :=
  ChartedSpace.preservesSmoothScalars_locallyRingedSpaceMap
    𝓘(𝕜, Plane 𝕜) emptyMap emptyMap_smooth

example :
    (ChartedSpace.locallyRingedSpaceMap
      (emptyMap (𝕜 := ℂ)) emptyMap_smooth).toHom =
    (ChartedSpace.locallyRingedSpaceMap (M := emptyDomain ℂ) (N := slab ℂ)
      ((ChartedSpace.locallyRingedSpaceMap emptyMap emptyMap_smooth).toHom.base :
        emptyDomain ℂ → slab ℂ)
      (empty_preserves (𝕜 := ℂ)).contMDiff_base).toHom :=
  (empty_preserves (𝕜 := ℂ)).eq_locallyRingedSpaceMap

end SmoothScalarReconstructionTest
