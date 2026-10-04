/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces

/-!
# Holomorphic scalar sections on complex domains

A nonconstant holomorphic function on the entire chart ball gives a section whose
value is computed through the complete restricted-ambient chart morphism.
Finite-dimensional complex balls exercise restriction and full sheaf precomposition.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace HolomorphicSectionsTest

open ChartedSpace

def disc : Opens ℂ := ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩

private def origin : disc := ⟨0, by simp [disc]⟩

example : (2 : ℂ) ∉ disc := by
  simp [disc, Metric.mem_ball, dist_eq_norm]

example : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
    (fun _ : (⊥ : Opens ℂ) ↦ (0 : ℂ)) :=
  mdifferentiable_const

example (D : Opens ℂ) (value : ℂ) :
    ∃ representativeSection :
        (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj (op (⊤ : Opens D)),
      ∀ point : (⊤ : Opens D), representativeSection point = value := by
  exact ⟨ComplexLine.ofHolomorphic D ⊤ (fun _ ↦ value) mdifferentiable_const,
    fun _ ↦ rfl⟩

private def chartData : ChartLocalBall (𝕜 := ℂ) (E := ℂ) (∞ : ℕ∞ω) origin :=
  chartLocalBall ∞ origin

private def representative (point : (⊤ : Opens chartData.ball)) : ℂ :=
  ((point : chartData.ball) : ℂ) + 2

private theorem representative_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) representative := by
  have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun point : (⊤ : Opens chartData.ball) ↦ ((point : chartData.ball) : ℂ)) :=
    ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num)).comp
      ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))
  exact hval.add mdifferentiable_const

private theorem representative_smooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ representative :=
  (ComplexLine.smooth_iff_holomorphic chartData.ball ⊤ representative).2
    representative_holomorphic

example : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) representative := by
  have hsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ representative :=
    (contMDiff_subtype_val.comp contMDiff_subtype_val).add contMDiff_const
  exact (ComplexLine.smooth_iff_holomorphic chartData.ball ⊤ representative).1 hsmooth

private def openRepresentative (point : disc) : ℂ := (point : ℂ) + 2

private theorem openRepresentative_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) openRepresentative := by
  have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : disc → ℂ) :=
    (contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num)
  exact hval.add mdifferentiable_const

private theorem openRepresentative_smooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ openRepresentative :=
  (ComplexLine.smooth_iff_holomorphic_open disc openRepresentative).2
    openRepresentative_holomorphic

example : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) openRepresentative := by
  have hsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ openRepresentative :=
    contMDiff_subtype_val.add contMDiff_const
  exact (ComplexLine.smooth_iff_holomorphic_open disc openRepresentative).1 hsmooth

private def translate (point : disc) : (⊤ : Opens ℂ) :=
  ⟨openRepresentative point, trivial⟩

private theorem translate_holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) translate := by
  have hsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ translate :=
    (ContMDiff.subtypeVal_comp_iff (⊤ : Opens ℂ) translate).mp openRepresentative_smooth
  exact hsmooth.mdifferentiable (by norm_num)

private def imageHalfDisc : Opens (⊤ : Opens ℂ) :=
  ⟨Metric.ball (⟨2, trivial⟩ : (⊤ : Opens ℂ)) (1 / 2), Metric.isOpen_ball⟩

private def imageCoordinate (point : imageHalfDisc) : ℂ := ((point : (⊤ : Opens ℂ)) : ℂ)

private theorem imageCoordinate_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) imageCoordinate :=
  ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num)).comp
    ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))

example : (translate origin : ℂ) ≠ (origin : ℂ) := by
  norm_num [translate, openRepresentative, origin]

private theorem origin_mem_preimage : origin ∈
    (Opens.map (TopCat.ofHom ⟨translate,
      (ComplexLine.holomorphic_contMDiff translate translate_holomorphic).continuous⟩)).obj
        imageHalfDisc := by
  change translate origin ∈ imageHalfDisc
  norm_num [translate, openRepresentative, origin, imageHalfDisc, Metric.mem_ball, dist_eq_norm]

private def outsidePreimage : disc :=
  ⟨(1 / 2 : ℂ), by norm_num [disc, Metric.mem_ball, dist_eq_norm]⟩

example : outsidePreimage ∉
    (Opens.map (TopCat.ofHom ⟨translate,
      (ComplexLine.holomorphic_contMDiff translate translate_holomorphic).continuous⟩)).obj
        imageHalfDisc := by
  change translate outsidePreimage ∉ imageHalfDisc
  norm_num [translate, openRepresentative, outsidePreimage, imageHalfDisc,
    Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]

example : ((ComplexLine.holomorphicSheafHom translate translate_holomorphic).hom.app
      (op imageHalfDisc)
      (ComplexLine.ofHolomorphic (⊤ : Opens ℂ) imageHalfDisc imageCoordinate
        imageCoordinate_holomorphic) :
      (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) disc ℂ).presheaf.obj
        (op ((Opens.map (TopCat.ofHom ⟨translate,
          (ComplexLine.holomorphic_contMDiff translate translate_holomorphic).continuous⟩)).obj
            imageHalfDisc))).1 ⟨origin, origin_mem_preimage⟩ = 2 := by
  rw [ComplexLine.holomorphicSheafHom_app_apply]
  norm_num [imageCoordinate, translate, openRepresentative, origin]

example : ((ComplexLine.holomorphicLocallyRingedSpaceMap translate translate_holomorphic).c.app
      (op imageHalfDisc)
      (ComplexLine.ofHolomorphic (⊤ : Opens ℂ) imageHalfDisc imageCoordinate
        imageCoordinate_holomorphic)) =
    ComplexLine.ofHolomorphic disc
      ((Opens.map (TopCat.ofHom ⟨translate,
        (ComplexLine.holomorphic_contMDiff translate translate_holomorphic).continuous⟩)).obj
        imageHalfDisc)
      (fun point ↦ imageCoordinate ⟨translate point.1, point.2⟩)
      (ComplexLine.holomorphic_precomp translate translate_holomorphic imageHalfDisc
        imageCoordinate imageCoordinate_holomorphic) := by
  exact ComplexLine.holomorphicLocallyRingedSpaceMap_c_app_ofHolomorphic
    translate translate_holomorphic imageHalfDisc imageCoordinate imageCoordinate_holomorphic

private def coordinate :
    (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) chartData.ball ℂ).presheaf.obj
      (op (⊤ : Opens chartData.ball)) :=
  ComplexLine.ofHolomorphic chartData.ball ⊤ representative representative_holomorphic

private def point : chartData.neighborhood := ⟨origin, chartData.mem_neighborhood⟩

private theorem coordinate_at_point : coordinate ⟨chartData.coord point, by simp⟩ = 2 := by
  change ((chartData.coord point : chartData.ball) : ℂ) + 2 = 2
  rw [chartData.coord_apply]
  change (chartAt ℂ (origin : ℂ)) (origin : ℂ) + 2 = 2
  simp [chartAt_self_eq, origin]

private def offCenter : chartData.ball :=
  ⟨(chartAt ℂ origin) origin + (chartData.radius / 2 : ℝ), by
    rw [chartData.mem_ball]
    have hr : 0 < chartData.radius / 2 := half_pos chartData.radius_pos
    have hlt : chartData.radius / 2 < chartData.radius := half_lt_self chartData.radius_pos
    calc
      dist ((chartAt ℂ origin) origin + (chartData.radius / 2 : ℝ))
          ((chartAt ℂ origin) origin) = ‖((chartData.radius / 2 : ℝ) : ℂ)‖ := by
            simp [dist_eq_norm]
      _ = chartData.radius / 2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      _ < chartData.radius := hlt⟩

example : ∃ first second : (⊤ : Opens chartData.ball),
    coordinate first ≠ coordinate second := by
  refine ⟨⟨chartData.center, by simp⟩, ⟨offCenter, by simp⟩, ?_⟩
  change (chartAt ℂ origin) origin + 2 ≠
    ((chartAt ℂ origin) origin + (chartData.radius / 2 : ℝ)) + 2
  intro heq
  have hz : ((chartData.radius / 2 : ℝ) : ℂ) = 0 := by
    have hbase := add_right_cancel heq.symm
    apply add_left_cancel (a := (chartAt ℂ origin) origin)
    simpa using hbase
  exact (ne_of_gt (half_pos chartData.radius_pos)) (Complex.ofReal_eq_zero.mp hz)

example : smoothSheafCommRing.eval 𝓘(ℂ) 𝓘(ℂ) chartData.neighborhood ℂ point
    ((smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) chartData.neighborhood ℂ).presheaf.germ
      ((Opens.map ((restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ)) (M := disc)
        chartData.neighborhood).inv ≫ chartData.smoothIso.hom).base).obj ⊤)
      point (by simp)
      (((restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ)) (M := disc)
        chartData.neighborhood).inv ≫
        chartData.smoothIso.hom).c.app (op (⊤ : Opens chartData.ball)) coordinate)) = 2 := by
  exact (chartData.smoothIso_hom_section_germ_eval ⊤ point (by simp) coordinate).trans
    coordinate_at_point

end HolomorphicSectionsTest

namespace FiniteDimensionalHolomorphicSectionsTest

open ChartedSpace

private abbrev Model := EuclideanSpace ℂ (Fin 2)

private def domain : Opens Model := ⟨Metric.ball (0 : Model) 1, Metric.isOpen_ball⟩

private def origin : domain := ⟨0, by simp [domain]⟩

private def quarter : domain :=
  ⟨EuclideanSpace.single (0 : Fin 2) (1 / 4 : ℂ), by
    norm_num [domain, Metric.mem_ball, dist_eq_norm, PiLp.norm_single]⟩

example : EuclideanSpace.single (0 : Fin 2) (2 : ℂ) ∉ domain := by
  norm_num [domain, Metric.mem_ball, dist_eq_norm, PiLp.norm_single]

private def squareCoordinate (point : domain) : ℂ :=
  (point.1 0) ^ 2 + point.1 1

private theorem coordinate_mdifferentiable (index : Fin 2) :
    MDifferentiable 𝓘(ℂ, Model) 𝓘(ℂ)
      (fun point : domain ↦ point.1 index) := by
  have hproj : Differentiable ℂ (fun point : Model ↦ point index) := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℂ) index).differentiable
  exact hproj.mdifferentiable.comp
    ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))

private theorem squareCoordinate_holomorphic :
    MDifferentiable 𝓘(ℂ, Model) 𝓘(ℂ) squareCoordinate :=
  ((coordinate_mdifferentiable 0).pow 2).add (coordinate_mdifferentiable 1)

example : (ComplexManifold.ofHolomorphic domain ⊤
    (fun point : (⊤ : Opens domain) ↦ squareCoordinate point.1)
    (squareCoordinate_holomorphic.comp
      ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))))
      ⟨origin, by simp⟩ = 0 := by
  norm_num [squareCoordinate, origin]

example : squareCoordinate origin = 0 ∧ squareCoordinate quarter = 1 / 16 := by
  norm_num [squareCoordinate, origin, quarter, PiLp.single_apply]

example : ContMDiff 𝓘(ℂ, Model) 𝓘(ℂ, ℂ × ℂ) ∞
    (fun point : domain ↦ ((point.1 0) ^ 2, (point.1 1) ^ 3)) := by
  apply (ComplexManifold.smooth_iff_holomorphic_open domain _).2
  exact ((coordinate_mdifferentiable 0).pow 2).prodMk_space
    ((coordinate_mdifferentiable 1).pow 3)

private def inner : Opens domain :=
  ⟨(Subtype.val : domain → Model) ⁻¹' Metric.ball 0 (3 / 4),
    Metric.isOpen_ball.preimage continuous_subtype_val⟩

private def topRepresentative (point : (⊤ : Opens domain)) : ℂ :=
  squareCoordinate point.1

private theorem topRepresentative_holomorphic :
    MDifferentiable 𝓘(ℂ, Model) 𝓘(ℂ) topRepresentative :=
  squareCoordinate_holomorphic.comp
    ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))

example : ∃ first second : (⊤ : Opens domain),
    (ComplexManifold.ofHolomorphic domain ⊤ topRepresentative
      topRepresentative_holomorphic) first ≠
    (ComplexManifold.ofHolomorphic domain ⊤ topRepresentative
      topRepresentative_holomorphic) second := by
  refine ⟨⟨origin, trivial⟩, ⟨quarter, trivial⟩, ?_⟩
  norm_num [topRepresentative, squareCoordinate, origin, quarter,
    PiLp.single_apply]

private def innerOrigin : inner := ⟨origin, by simp [inner, origin]⟩

example : quarter ∈ inner := by
  norm_num [inner, quarter, Metric.mem_ball, dist_eq_norm, PiLp.norm_single]

private def nearBoundary : domain :=
  ⟨EuclideanSpace.single (0 : Fin 2) (7 / 8 : ℂ), by
    norm_num [domain, Metric.mem_ball, dist_eq_norm, PiLp.norm_single]⟩

example : nearBoundary ∉ inner := by
  norm_num [inner, nearBoundary, Metric.mem_ball, dist_eq_norm, PiLp.norm_single]

example :
    ((smoothSheafCommRing 𝓘(ℂ, Model) 𝓘(ℂ) domain ℂ).presheaf.map
        (show inner ≤ (⊤ : Opens domain) from le_top).hom.op
        (ComplexManifold.ofHolomorphic domain ⊤ topRepresentative
          topRepresentative_holomorphic)).1 innerOrigin = 0 := by
  rw [ComplexManifold.ofHolomorphic_restrict]
  norm_num [topRepresentative, squareCoordinate, innerOrigin, origin]

example (f : (⊥ : Opens Model) → ℂ) :
    ContMDiff 𝓘(ℂ, Model) 𝓘(ℂ) ∞ f := by
  apply (ComplexManifold.smooth_iff_holomorphic_open (⊥ : Opens Model) f).2
  intro point
  exact False.elim point.2

private abbrev ZeroModel := EuclideanSpace ℂ (Fin 0)

private def zeroPoint : (⊤ : Opens (⊤ : Opens ZeroModel)) :=
  ⟨⟨0, trivial⟩, trivial⟩

example : ComplexManifold.ofHolomorphic (⊤ : Opens ZeroModel) ⊤
    (fun _ : (⊤ : Opens (⊤ : Opens ZeroModel)) ↦ (7 : ℂ)) mdifferentiable_const
      zeroPoint = 7 := rfl

private def projection (point : domain) : (⊤ : Opens ℂ) :=
  ⟨point.1 0 + 1 / 4, trivial⟩

private theorem projection_holomorphic :
    MDifferentiable 𝓘(ℂ, Model) 𝓘(ℂ) projection := by
  have hcoord : ContMDiff 𝓘(ℂ, Model) 𝓘(ℂ) ∞
      (fun point : domain ↦ point.1 0) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).contMDiff.comp contMDiff_subtype_val
  have hvalue : ContMDiff 𝓘(ℂ, Model) 𝓘(ℂ) ∞
      (fun point : domain ↦ point.1 0 + 1 / 4) := hcoord.add contMDiff_const
  exact ((ContMDiff.subtypeVal_comp_iff (⊤ : Opens ℂ) projection).mp hvalue).mdifferentiable
    (by norm_num)

private def imageDisc : Opens (⊤ : Opens ℂ) :=
  ⟨(Subtype.val : (⊤ : Opens ℂ) → ℂ) ⁻¹' Metric.ball 0 (1 / 2),
    Metric.isOpen_ball.preimage continuous_subtype_val⟩

private def imageRepresentative (point : imageDisc) : ℂ := (point.1 : ℂ)

private theorem imageRepresentative_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) imageRepresentative :=
  ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num)).comp
    ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))

private theorem origin_mem_preimage : origin ∈
    (Opens.map (TopCat.ofHom ⟨projection,
      (ComplexManifold.holomorphic_contMDiff projection projection_holomorphic).continuous⟩)).obj
        imageDisc := by
  change projection origin ∈ imageDisc
  norm_num [projection, origin, imageDisc, Metric.mem_ball, dist_eq_norm]

example : quarter ∉
    (Opens.map (TopCat.ofHom ⟨projection,
      (ComplexManifold.holomorphic_contMDiff projection projection_holomorphic).continuous⟩)).obj
        imageDisc := by
  change projection quarter ∉ imageDisc
  norm_num [projection, quarter, imageDisc, Metric.mem_ball, dist_eq_norm,
    PiLp.single_apply]

example : ((ComplexManifold.holomorphicLocallyRingedSpaceMap projection
      projection_holomorphic).c.app (op imageDisc)
      (ComplexManifold.ofHolomorphic (⊤ : Opens ℂ) imageDisc imageRepresentative
        imageRepresentative_holomorphic) :
      (smoothSheafCommRing 𝓘(ℂ, Model) 𝓘(ℂ) domain ℂ).presheaf.obj
        (op ((Opens.map (TopCat.ofHom ⟨projection,
          (ComplexManifold.holomorphic_contMDiff projection
            projection_holomorphic).continuous⟩)).obj
            imageDisc))).1 ⟨origin, origin_mem_preimage⟩ = 1 / 4 := by
  have heval := ComplexManifold.holomorphicLocallyRingedSpaceMap_c_app_apply
    projection projection_holomorphic imageDisc
    (ComplexManifold.ofHolomorphic (⊤ : Opens ℂ) imageDisc imageRepresentative
      imageRepresentative_holomorphic) ⟨origin, origin_mem_preimage⟩
  exact heval.trans (by norm_num [imageRepresentative, projection, origin])

end FiniteDimensionalHolomorphicSectionsTest

namespace HolomorphicHelperGeneralityTest

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]

example (D : Opens E) {V W : Opens D} (h : W ≤ V) (g : V → ℂ)
    (hg : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ) g) :
    Continuous (fun point : W ↦ g ⟨point.1, h point.2⟩) :=
  (ComplexManifold.holomorphic_restrict D h g hg).continuous

example {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (V : Opens G)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ) g) :
    Continuous (fun point : (⟨f ⁻¹' (V : Set G), V.isOpen.preimage hf.continuous⟩ : Opens D) ↦
      g ⟨f point.1, point.2⟩) :=
  (ComplexManifold.holomorphic_precomp f hf V g hg).continuous

example [FiniteDimensional ℂ E] [CompleteSpace F] {D : Opens E} {G : Opens F}
    (f : D → G) (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) :
    Continuous f :=
  (ComplexManifold.holomorphic_contMDiff f hf).continuous

end HolomorphicHelperGeneralityTest

namespace SmoothSectionGeneralityTest

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

example (D : Opens E) (V : Opens D)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ).presheaf.obj (op V)) :
    Continuous (fun point : V ↦ representativeSection point) :=
  (ComplexManifold.section_holomorphic D V representativeSection).continuous

end SmoothSectionGeneralityTest
