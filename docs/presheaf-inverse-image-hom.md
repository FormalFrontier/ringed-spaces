# Hom adjunction for inverse-image module presheaves

Import `RingedSpaces.Modules.PresheafInverseImageHom` (or `RingedSpaces`). All
new declarations are in `RingedSpaces.Modules.PresheafInverseImage`. This is a
presheaf-of-modules construction, not a sheaf or stalk construction.

## Mathematical setting

Let `X Y : TopCat.{v}`, `f : X ⟶ Y` be an arbitrary continuous map and
`R : Y.Presheaf RingCat.{v}` a presheaf of potentially **noncommutative** rings.
Set `F := (Opens.map f).op`, `K := F.pointwiseLeftKanExtension R`, and let
`u := F.pointwiseLeftKanExtensionUnit R : R ⟶ F ⋙ K`. The functor
`inverseImageFunctor f R : PresheafOfModules R ⥤ PresheafOfModules K` uses
the pointwise neighborhood-colimit module action, not a separately chosen
left adjoint. Its right adjoint is the **native**
`PresheafOfModules.pushforward (F := Opens.map f) u`. Ring and module carriers,
the site and its morphisms use the same universe `v`.

For any `M` over `R` and `N` over `K`, `homEquiv f R M N` is an equivalence of
**bundled linear morphisms**

```text
(inverseImageFunctor f R).obj M ⟶ N
    ≃ M ⟶ (PresheafOfModules.pushforward u).obj N.
```

`adjunction f R` packages this natural equivalence into an adjunction. The
construction assumes neither nonempty spaces nor nonzero rings, and imposes no
sheaf, commutativity, openness, or finiteness condition.

## Section formulas and proof

The forward map `forward f R g` sends `m : M(V)` to
`g_(f⁻¹V)(u_M,V(m))`, where `u_M` is the *actual additive pointwise-Kan
unit*. `forward_apply` records this formula. Its source-ring linearity follows
from `unit_smul`: `u_M,V(r • m) = u_R,V(r) • u_M,V(m)` for every `r : R(V)`;
then apply the linearity of `g`. The additive underlying map is the composition
of `u_M`, whiskering `g`, and the inverse native
`pushforwardCompToPresheaf` comparison; `PresheafOfModules.homMk` bundles it.

The inverse `backward f R h` uses the native pointwise Kan
`descOfIsLeftKanExtension` on the underlying additive presheaves. If `i` is a
neighborhood of an open `U` and `ιᵢ(m)` its colimit generator, `backward_ι`
states

```text
(backward f R h)_U(ιᵢ(m)) = N.map i.hom (h_(i.left)(m)).
```

An **arbitrary** coefficient `r : K(U)` and module section of the inverse
image at `U` have representatives `ιᵢ(a)` and `ιᵢ(b)` at the *same* `i`, by
`pointwise_jointly_surjective`. The actual `pointwise_smul_ι` identifies
their product with `ιᵢ(a • b)`. The ring colimit generator satisfies
`ιᵢ(a) = K.map i.hom (u_R,i.left(a))`, by `ring_map_ι` and the genuine ring
unit. Sectionwise linearity of `h` through `u_R` and semilinearity of
`N.map i.hom` finish the calculation. Thus `backward_smul` applies to every
coefficient, *not just* those in the direct image of `u_R`.

`backward_forward` follows from uniqueness of Kan descent after precomposing
with `u_M` and faithful forgetting. `forward_backward` follows by the descent
formula at the identity neighborhood. `forward_naturality_left` and
`forward_naturality_right` establish naturality for arbitrary morphisms in
both variables; `backward_naturality_left/right` transport those identities
through the inverse equivalence. Native `Adjunction.mkOfHomEquiv` provides
the triangle identities, exercised in the saved clients.

`unit_apply` identifies the **module** unit section with `u_M`; `counit_ι`
identifies the **module** counit on every neighborhood generator with the
restriction `N.map i.hom`. `unit_naturality` and `counit_naturality` are
the corresponding identities for arbitrary module morphisms. The theorem
`forward_underlying_additive` identifies the **entire** underlying forward
map with the ordinary additive pullback/pushforward transpose after composing
with `(underlyingComparison f R).inv.app M` (the inverse orientation), rather
than claiming equality of separately chosen pullback objects.

For an executable, generic API example, see
`RingedSpacesTests/PresheafInverseImageHom.lean`; for a nonidentity continuous map and a
nonempty proper open, see `RingedSpacesTests/PresheafInverseImageHomConcrete.lean`.

## Reproducibility

This library's sole direct dependency is mathlib, at the exact revision in
`lakefile.toml`; use the pinned `lean-toolchain`. Before any build, execute
`lake exe cache get`. The focused import and saved clients can then be built
with `lake --wfail build RingedSpaces.Modules.PresheafInverseImageHom
RingedSpacesTests.PresheafInverseImageHom RingedSpacesTests.PresheafInverseImageHomConcrete
RingedSpacesTests.PresheafInverseImageHomRoot RingedSpacesTests.PresheafInverseImageHomAxioms`.
Historical contributor and source-adaptation credit is in `NOTICE.md`.
Prior author-side checks and review records are preserved separately from
this mathematical guide in the pre-release evidence archive.
