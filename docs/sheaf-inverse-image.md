# Sheaf inverse image of modules

Import `RingedSpaces` for the complete API, or import
`RingedSpaces.Modules.SheafInverseImageHom` directly; the narrower
`RingedSpaces.Modules.SheafInverseImage` provides the functor and comparison.
The [root-only client](../RingedSpacesTests/SheafInverseImageRoot.lean) uses only the public
aggregate. These modules need only the pinned mathlib dependency and the
library's public presheaf inverse-image modules; no research repository is
required by clients.

Fix a single universe `v`, spaces `X Y : TopCat.{v}`, a continuous morphism
`f : X ⟶ Y`, and a commutative ring sheaf `S : Y.Sheaf CommRingCat.{v}`.
No nonemptiness, reducedness, nonzero-ring, or finiteness assumption is used.
`sheafForget T` is the functor that forgets commutativity of ring sheaves on `T`.
Write `R := (sheafForget Y).obj S` and
`R' := (sheafForget X).obj ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S)`.

## Construction

The namespace is `RingedSpaces.Modules.SheafInverseImage`.

- `moduleFunctor f S : SheafOfModules R ⥤ SheafOfModules R'` takes the
  *actual* neighborhood-colimit module presheaf, sheafifies it over the
  sheafification of the pointwise ring, and restricts its scalars along the
  genuine comparison to `R'`. It works on morphisms, not just objects.
- `moduleUnderlyingNatIso f S` identifies the functor's underlying additive
  sheaf with `SheafOfModules.toSheaf R ⋙ TopCat.Sheaf.pullback
  AddCommGrpCat.{v} f`, naturally for every module morphism.
- `comparisonNatIso f` compares the *nonidentical* functors
  `TopCat.Sheaf.pullback CommRingCat.{v} f ⋙ sheafForget X` and
  `sheafForget Y ⋙ TopCat.Sheaf.pullback RingCat.{v} f`.
  `comparison_unit f S` proves equality of entire ring-sheaf maps between
  the actual forgotten commutative-ring unit, followed by this comparison,
  and the actual ordinary-ring inverse-image unit.
- `PresheafInverseImage.inverseImageSheafModule` and
  `PresheafInverseImage.inverseImageSheafRingComparison` expose the native
  sheafification and the chosen-ring comparison independently of `S`.

## Adjunction

`actualUnit f S : R ⟶ (TopCat.Sheaf.pushforward RingCat.{v} f).obj R'`
forgets the **actual** commutative-ring sheaf pullback/pushforward unit.
`ringUnit_iso` proves its complete ring-map compatibility with sheafified
pointwise colimit coefficients; it does not assume the two ring pullbacks
coincide by definition. The right adjoint is the native
`pushforwardFunctor f S`, pushing modules through `actualUnit f S`.

For module sheaves `M` over `R` and `N` over `R'`, the equivalence

```text
homEquiv f S M N : ((moduleFunctor f S).obj M ⟶ N)
  ≃ (M ⟶ (pushforwardFunctor f S).obj N)
```

is between **bundled linear maps**, natural in both variables; its inverse
uses pointwise Kan descent and the native sheafification Hom equivalence.
`adjunction f S : moduleFunctor f S ⊣ pushforwardFunctor f S` packages these
maps into the actual unit and counit. `unit_app_eq`, `counit_app_eq`,
`left_triangle`, and `right_triangle` expose their equations. Theorems
`forward_underlying`, `forward_underlying_additive`,
`backward_underlying_additive`, and `unit_underlying` identify the **whole**
underlying additive sheaf morphisms, not just selected section generators.

The local filtered-neighborhood instance exists solely to reconstruct the
CommRing/Ring colimit comparison: the original presheaf module's instance is
private. The module action and presheaf Hom adjunction are reused rather than
re-implemented. The allowed foundations for completed results are `propext`,
`Classical.choice`, and `Quot.sound`; acceptance requires checking the actual
transitive axiom evidence for the exact build.

## Provenance and reproducibility

Formal Frontier contributors adapted earlier module-action, presheaf Hom,
sheaf-coherence and sheaf Hom research into this independent mathematical
library; see [attribution](../NOTICE.md). No research repository is a build
dependency. Reproduce with Lean `v4.34.0-rc2`, mathlib revision
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, then run
`lake exe cache get` **before** targeted `lake --wfail build` commands.
