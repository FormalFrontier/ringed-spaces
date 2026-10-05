/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.Complex.Holomorphic
public import RingedSpaces.ChartedSpace.SmoothLocalBall

/-!
# Holomorphic sections on finite-dimensional complex domains

On open subtypes of finite-dimensional complex normed spaces, holomorphic scalar
functions are precisely the sections of the existing complex-smooth scalar sheaf. They retain
the sheaf's restriction, germ and whole-morphism operations; no second sheaf
or locally ringed space is introduced.

The chartwise comparison assumes a smooth manifold structure; it does not
upgrade a merely holomorphic atlas. The scalar sheaf uses the common-universe
convention of `smoothSheafCommRing`, while the pure differentiability helpers
permit independent source and target universes without sheaf-specific hypotheses.

## References

* Formal Frontier, `ComplexAnalysis/Analysis/Complex/FiniteDimensional.lean`:
  finite-dimensional complex analyticity, used through the smoothness bridge
  in `RingedSpaces.Complex.Holomorphic`.
* Mathlib, `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean` (Heather Macbeth and
  Adam Topaz): the existing smooth scalar-function sheaf used for holomorphic sections.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025
  draft), Definition 4.3.9 (p. 142): motivation for holomorphic local-function
  models, not a proof of this own- and nested-open section identification with
  the canonical complex-smooth scalar sheaf or an arbitrary-sheaf reconstruction.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

universe u v w

namespace ComplexManifold

local instance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] : CompleteSpace V :=
  FiniteDimensional.complete ℂ V

/-- Complex smoothness of a map from a smooth manifold modeled on a finite-dimensional
complex normed space is equivalent to complex manifold differentiability. -/
theorem contMDiff_iff_mdifferentiable
    {E : Type u} {M : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : M → F) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f ↔
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f := by
  constructor
  · intro hf
    exact hf.mdifferentiable (by norm_num)
  · intro hf point
    have hdiff : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, F)
        (f ∘ (extChartAt 𝓘(ℂ, E) point).symm) (extChartAt 𝓘(ℂ, E) point).target :=
      hf.comp_mdifferentiableOn mdifferentiableOn_extChartAt_symm
    have hsmooth :=
      (contMDiffOn_iff_mdifferentiableOn_complex_of_finiteDimensional
        (isOpen_extChartAt_target point)).2 hdiff
    apply (contMDiffAt_iff_source_of_mem_source (mem_chart_source E point)).2
    simpa only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] using
      hsmooth.contMDiffAt (extChartAt_target_mem_nhds point)

/-- A function defined on an open finite-dimensional complex domain is smooth
exactly when it is holomorphic on that domain; no extension is required. -/
theorem smooth_iff_holomorphic_open
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (U : Opens E) (f : U → F) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f ↔
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f :=
  contMDiff_iff_mdifferentiable f

/-- Holomorphicity on a nested open subtype agrees with its own complex
smoothness, without assuming an extension to the outer domain. -/
theorem smooth_iff_holomorphic
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (D : Opens E) (V : Opens D) (f : V → F) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f ↔
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f :=
  contMDiff_iff_mdifferentiable f

/-- Restriction of a holomorphic representative is holomorphic. -/
theorem holomorphic_restrict
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Opens E) {V W : Opens D} (h : W ≤ V)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ)
      (fun point : W ↦ f ⟨point.1, h point.2⟩) :=
  hf.comp ((contMDiff_inclusion (n := 1) h).mdifferentiable (by norm_num))

/-- Holomorphic maps between open complex domains are smooth when the source
is finite-dimensional and the target is complete. -/
theorem holomorphic_contMDiff
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f := by
  have hsubtype : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, F) ∞ (Subtype.val : G → F) :=
    contMDiff_subtype_val
  have hval : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) (Subtype.val ∘ f) :=
    (hsubtype.mdifferentiable (by norm_num)).comp hf
  have hsmooth := (smooth_iff_holomorphic_open D (Subtype.val ∘ f)).2 hval
  exact (ContMDiff.subtypeVal_comp_iff G f).mp hsmooth

/-- Precomposing a holomorphic representative remains holomorphic on its
inverse-image open. -/
theorem holomorphic_precomp
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (V : Opens G)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ) g) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ)
      (fun point : (⟨f ⁻¹' (V : Set G), V.isOpen.preimage hf.continuous⟩ : Opens D) ↦
        g ⟨f point.1, point.2⟩) := by
  have hmap : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F)
      (fun point : (⟨f ⁻¹' (V : Set G), V.isOpen.preimage hf.continuous⟩ : Opens D) ↦
        (⟨f point.1, point.2⟩ : V)) := by
    intro point
    have hval : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F)
        (fun point : (⟨f ⁻¹' (V : Set G), V.isOpen.preimage hf.continuous⟩ : Opens D) ↦
          f point.1) point :=
      (hf.comp ((contMDiff_subtype_val (n := 1)).mdifferentiable (by norm_num))) point
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ Set.univ point).mp hval
  exact hg.comp hmap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Bundle a holomorphic scalar function as a section of the existing smooth
scalar sheaf. -/
def ofHolomorphic (D : Opens E) (V : Opens D) (f : V → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ) f) :
    (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ).presheaf.obj (op V) :=
  ⟨f, (smooth_iff_holomorphic D V f).2 hf⟩

/-- The bundled section evaluates to its original representative. -/
@[simp] theorem ofHolomorphic_apply (D : Opens E) (V : Opens D) (f : V → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ) f) (point : V) :
    ofHolomorphic D V f hf point = f point := rfl

/-- Germ evaluation recovers the value of the holomorphic representative. -/
@[simp] theorem ofHolomorphic_eval_germ (D : Opens E) (V : Opens D)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ) f)
    (point : D) (hpoint : point ∈ V) :
    smoothSheafCommRing.eval 𝓘(ℂ, E) 𝓘(ℂ) D ℂ point
      ((smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ).presheaf.germ V point hpoint
        (ofHolomorphic D V f hf)) = f ⟨point, hpoint⟩ :=
  smoothSheafCommRing.eval_germ V point hpoint (ofHolomorphic D V f hf)

omit [FiniteDimensional ℂ E] in
/-- Every smooth scalar section on a complex domain is holomorphic. -/
theorem section_holomorphic (D : Opens E) (V : Opens D)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ).presheaf.obj (op V)) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ) (fun point : V ↦ representativeSection point) :=
  ContMDiff.mdifferentiable representativeSection.2 (by norm_num)

omit [FiniteDimensional ℂ E] in
/-- Sections are equal if they have the same values everywhere. -/
@[ext] theorem section_ext (D : Opens E) (V : Opens D)
    {first second : (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ).presheaf.obj (op V)}
    (h : ∀ point : V, first point = second point) : first = second := by
  apply Subtype.ext
  exact funext h

/-- Bundling a holomorphic representative commutes with restriction. -/
theorem ofHolomorphic_restrict (D : Opens E) {V W : Opens D} (h : W ≤ V)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ) f) :
    (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ).presheaf.map h.hom.op
        (ofHolomorphic D V f hf) =
      ofHolomorphic D W (fun point : W ↦ f ⟨point.1, h point.2⟩)
        (holomorphic_restrict D h f hf) := by
  apply section_ext D W
  intro point
  rfl

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The existing smooth-scalar-sheaf morphism induced by holomorphic precomposition. -/
def holomorphicSheafHom [CompleteSpace F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) :
    smoothSheafCommRing 𝓘(ℂ, F) 𝓘(ℂ) G ℂ ⟶
      (TopCat.Sheaf.pushforward _
        (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj
          (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ) :=
  (holomorphic_contMDiff f hf).smoothSheafCommRingHom 𝓘(ℂ, F) G f

/-- The induced sheaf morphism evaluates by precomposition. -/
@[simp] theorem holomorphicSheafHom_app_apply [CompleteSpace F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (V : Opens G)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ, F) 𝓘(ℂ) G ℂ).presheaf.obj (op V))
    (point : (Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V) :
    ((holomorphicSheafHom f hf).hom.app (op V) representativeSection :
        (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ).presheaf.obj
          (op ((Opens.map (TopCat.ofHom
            ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V))).1 point =
      representativeSection ⟨f point.1, point.2⟩ := rfl

/-- The sheaf map takes a holomorphic section to its precomposition section. -/
theorem holomorphicSheafHom_app_ofHolomorphic [FiniteDimensional ℂ F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (V : Opens G)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ) g) :
    (holomorphicSheafHom f hf).hom.app (op V) (ofHolomorphic G V g hg) =
      ofHolomorphic D
        ((Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V)
        (fun point ↦ g ⟨f point.1, point.2⟩)
        (holomorphic_precomp f hf V g hg) := by
  apply section_ext D _
  intro point
  exact holomorphicSheafHom_app_apply f hf V _ point

/-- The full locally ringed-space map induced by holomorphic precomposition. -/
def holomorphicLocallyRingedSpaceMap [CompleteSpace F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ, E) D ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, F) G :=
  ChartedSpace.locallyRingedSpaceMap f (holomorphic_contMDiff f hf)

/-- The holomorphic identity induces the identity full morphism. -/
@[simp] theorem holomorphicLocallyRingedSpaceMap_id (D : Opens E) :
    holomorphicLocallyRingedSpaceMap (id : D → D) mdifferentiable_id =
      𝟙 (ChartedSpace.locallyRingedSpace 𝓘(ℂ, E) D) := rfl

/-- Full holomorphic precomposition morphisms preserve composition. -/
theorem holomorphicLocallyRingedSpaceMap_comp
    [FiniteDimensional ℂ F]
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {D : Opens E} {G : Opens F} {J : Opens H}
    (f : D → G) (g : G → J)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f)
    (hg : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, H) g) :
    holomorphicLocallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      holomorphicLocallyRingedSpaceMap f hf ≫
        holomorphicLocallyRingedSpaceMap g hg := rfl

/-- The sheaf component of the full map is the existing sheaf morphism. -/
theorem holomorphicLocallyRingedSpaceMap_c [CompleteSpace F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) :
    (holomorphicLocallyRingedSpaceMap f hf).c = (holomorphicSheafHom f hf).hom := rfl

/-- The full map's sheaf component evaluates by precomposition. -/
@[simp] theorem holomorphicLocallyRingedSpaceMap_c_app_apply
    [CompleteSpace F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (V : Opens G)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ, F) 𝓘(ℂ) G ℂ).presheaf.obj (op V))
    (point : (Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V) :
    ((holomorphicLocallyRingedSpaceMap f hf).c.app (op V) representativeSection :
        (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) D ℂ).presheaf.obj
          (op ((Opens.map (TopCat.ofHom
            ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V))).1 point =
      representativeSection ⟨f point.1, point.2⟩ := by
  rw [holomorphicLocallyRingedSpaceMap_c]
  exact holomorphicSheafHom_app_apply f hf V representativeSection point

/-- The full map's sheaf component sends a holomorphic representative to
its precomposition section. -/
theorem holomorphicLocallyRingedSpaceMap_c_app_ofHolomorphic
    [FiniteDimensional ℂ F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (V : Opens G)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ) g) :
    (holomorphicLocallyRingedSpaceMap f hf).c.app (op V) (ofHolomorphic G V g hg) =
      ofHolomorphic D
        ((Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V)
        (fun point ↦ g ⟨f point.1, point.2⟩)
        (holomorphic_precomp f hf V g hg) := by
  rw [holomorphicLocallyRingedSpaceMap_c]
  exact holomorphicSheafHom_app_ofHolomorphic f hf V g hg

end ComplexManifold

namespace ComplexLine

/-- A function on an open complex domain is complex-smooth exactly when it is
complex differentiable on its own domain, without requiring a global extension. -/
theorem smooth_iff_holomorphic_open (U : Opens ℂ) (f : U → ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  ComplexManifold.smooth_iff_holomorphic_open U f

/-- On a nested open subtype `V : Opens D`, holomorphicity is equivalent to
complex smoothness without requiring extension of `f` to the outer domain. -/
theorem smooth_iff_holomorphic (D : Opens ℂ) (V : Opens D) (f : V → ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  ComplexManifold.smooth_iff_holomorphic D V f

/-- Regard a holomorphic representative as a section of the canonical
complex-smooth scalar sheaf on its open domain. -/
def ofHolomorphic (D : Opens ℂ) (V : Opens D) (f : V → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj (op V) :=
  ComplexManifold.ofHolomorphic D V f hf

/-- The canonical section retains the values of the holomorphic representative. -/
@[simp] theorem ofHolomorphic_apply (D : Opens ℂ) (V : Opens D) (f : V → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (point : V) :
    ofHolomorphic D V f hf point = f point := rfl

/-- Evaluation of the canonical germ of a holomorphic representative returns
its value at the point. -/
@[simp] theorem ofHolomorphic_eval_germ (D : Opens ℂ) (V : Opens D)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (point : D) (hpoint : point ∈ V) :
    smoothSheafCommRing.eval 𝓘(ℂ) 𝓘(ℂ) D ℂ point
      ((smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.germ V point hpoint
        (ofHolomorphic D V f hf)) = f ⟨point, hpoint⟩ := by
  exact smoothSheafCommRing.eval_germ V point hpoint (ofHolomorphic D V f hf)

/-- A section of the canonical complex-smooth scalar sheaf is holomorphic. -/
theorem section_holomorphic (D : Opens ℂ) (V : Opens D)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj (op V)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun point : V ↦ representativeSection point) :=
  ComplexManifold.section_holomorphic D V representativeSection

/-- Smooth scalar sections on an open complex domain are determined pointwise. -/
@[ext] theorem section_ext (D : Opens ℂ) (V : Opens D)
    {first second : (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj (op V)}
    (h : ∀ point : V, first point = second point) : first = second :=
  ComplexManifold.section_ext D V h

/-- Holomorphic representatives restrict holomorphically to smaller opens. -/
theorem holomorphic_restrict (D : Opens ℂ) {V W : Opens D} (h : W ≤ V)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun point : W ↦ f ⟨point.1, h point.2⟩) :=
  ComplexManifold.holomorphic_restrict D h f hf

/-- Bundling a holomorphic representative commutes with canonical restriction. -/
theorem ofHolomorphic_restrict (D : Opens ℂ) {V W : Opens D} (h : W ≤ V)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.map h.hom.op
        (ofHolomorphic D V f hf) =
      ofHolomorphic D W (fun point : W ↦ f ⟨point.1, h point.2⟩)
        (holomorphic_restrict D h f hf) :=
  ComplexManifold.ofHolomorphic_restrict D h f hf

/-- Holomorphic precomposition between open complex domains is complex-smooth. -/
theorem holomorphic_contMDiff {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f :=
  ComplexManifold.holomorphic_contMDiff f hf

/-- Holomorphic precomposition uses the existing whole sheaf morphism. -/
def holomorphicSheafHom {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) E ℂ ⟶
      (TopCat.Sheaf.pushforward _
        (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj
          (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ) :=
  ComplexManifold.holomorphicSheafHom f hf

/-- The sheaf map induced by a holomorphic map evaluates by precomposition on
the inverse image of an open set. -/
@[simp] theorem holomorphicSheafHom_app_apply {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) E ℂ).presheaf.obj (op V))
    (point : (Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V) :
    ((holomorphicSheafHom f hf).hom.app (op V) representativeSection :
        (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj
          (op ((Opens.map (TopCat.ofHom
            ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V))).1 point =
      representativeSection ⟨f point.1, point.2⟩ := rfl

/-- Precomposing a holomorphic representative with a holomorphic map is holomorphic
on the inverse image of its domain. -/
theorem holomorphic_precomp {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun point : (Opens.map (TopCat.ofHom
        ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V ↦
        g ⟨f point.1, point.2⟩) :=
  ComplexManifold.holomorphic_precomp f hf V g hg

/-- The sheaf map takes a holomorphic section to the section represented by
precomposition on the inverse-image open. -/
theorem holomorphicSheafHom_app_ofHolomorphic {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    (holomorphicSheafHom f hf).hom.app (op V) (ofHolomorphic E V g hg) =
      ofHolomorphic D
        ((Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V)
        (fun point ↦ g ⟨f point.1, point.2⟩)
        (holomorphic_precomp f hf V g hg) := by
  apply section_ext D _
  intro point
  exact holomorphicSheafHom_app_apply f hf V _ point

/-- The existing full locally ringed-space morphism associated to holomorphic
precomposition between open complex domains. -/
def holomorphicLocallyRingedSpaceMap {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ) D ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ) E :=
  ComplexManifold.holomorphicLocallyRingedSpaceMap f hf

/-- The full map induced by the holomorphic identity is the identity morphism. -/
@[simp] theorem holomorphicLocallyRingedSpaceMap_id (D : Opens ℂ) :
    holomorphicLocallyRingedSpaceMap (id : D → D) mdifferentiable_id =
      𝟙 (ChartedSpace.locallyRingedSpace 𝓘(ℂ) D) := by
  rfl

/-- The full morphisms, including their sheaf maps, respect composition. -/
theorem holomorphicLocallyRingedSpaceMap_comp {D E F : Opens ℂ}
    (f : D → E) (g : E → F)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    holomorphicLocallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      holomorphicLocallyRingedSpaceMap f hf ≫
        holomorphicLocallyRingedSpaceMap g hg := by
  rfl

/-- The sheaf component of the full holomorphic-precomposition morphism is
the existing smooth scalar sheaf morphism. -/
theorem holomorphicLocallyRingedSpaceMap_c {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (holomorphicLocallyRingedSpaceMap f hf).c = (holomorphicSheafHom f hf).hom := rfl

/-- The sheaf component of the full locally ringed-space map precomposes
sections on inverse-image opens. -/
@[simp] theorem holomorphicLocallyRingedSpaceMap_c_app_apply {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) E ℂ).presheaf.obj (op V))
    (point : (Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V) :
    ((holomorphicLocallyRingedSpaceMap f hf).c.app (op V) representativeSection :
        (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj
          (op ((Opens.map (TopCat.ofHom
            ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V))).1 point =
      representativeSection ⟨f point.1, point.2⟩ := by
  rw [holomorphicLocallyRingedSpaceMap_c]
  exact holomorphicSheafHom_app_apply f hf V representativeSection point

/-- The full locally ringed-space map takes holomorphic sections to their
precompositions on inverse-image opens. -/
theorem holomorphicLocallyRingedSpaceMap_c_app_ofHolomorphic {D E : Opens ℂ}
    (f : D → E) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    (holomorphicLocallyRingedSpaceMap f hf).c.app (op V) (ofHolomorphic E V g hg) =
      ofHolomorphic D
        ((Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V)
        (fun point ↦ g ⟨f point.1, point.2⟩)
        (holomorphic_precomp f hf V g hg) := by
  rw [holomorphicLocallyRingedSpaceMap_c]
  exact holomorphicSheafHom_app_ofHolomorphic f hf V g hg

end ComplexLine
