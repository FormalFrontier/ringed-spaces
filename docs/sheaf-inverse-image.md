# Sheaf inverse image of modules

Import `RingedSpaces` for the complete API, or import
`RingedSpaces.Modules.SheafInverseImageHom` directly; the narrower
`RingedSpaces.Modules.SheafInverseImage` provides the functor and comparison.
The [root-only client](../Test/SheafInverseImageRoot.lean) uses only the public
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
re-implemented. The only required foundations for completed results are
`propext`, `Classical.choice`, and `Quot.sound` (verify the exact pinned build's
actual axiom receipts before accepting any result). The sheaf leaves received
bounded owner acceptance as preparation. Their root exports are part of the
combined module-sheaf and full-morphism assembly. Earlier preparation alone does
not establish this assembly's integration, release or source coverage.

## Provenance and reproducibility

The accepted source precursors were produced by Tasks
`hive-request-ed585cec87f054b23a8f72d6c5882b0f6753bc73`
(UID `c4410aab-4878-47a4-aa7f-0e50bd436202`),
`hive-request-a71657830db53cd29881f0026fa8b5e3d6a9ef3c`
(UID `a78a3887-0c81-4d19-9348-781caa1bce1c`),
`hive-request-724a310985250437cd65e489d2a64be08ee12871`
(UID `1e63d20e-3f1e-43da-8f6b-4f17e60020f4`), and
`hive-request-73dc549815be100a03dd91d507a98ee9f7e396cd`
(UID `c1aa7177-6bf6-4ff5-9a2b-8cdda8317c5d`). This independent library
preparation is by `hive-request-8f33afe07a3ab0de314522e27f4bbaec2df1940d`
(UID `30841a63-6910-4c7d-8c48-ddb0f57c9b58`). The mathematical source is
not a build dependency. Reproduce with Lean `v4.34.0-rc2`, mathlib revision
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, then run
`lake exe cache get` **before** targeted `lake --wfail build` commands. Exact
candidate-branch check receipts and their limits belong to the separate
evidence branch, not to the mathematical modules.
