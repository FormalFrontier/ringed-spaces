<!-- SPDX-License-Identifier: Apache-2.0 -->

# Ringed-space module square pasting

Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
draft), Exercise 7.2.D(f) (p. 205) and §2.7.4 (p. 94), motivate the natural
push–pull map for any full commutative square, not necessarily Cartesian and
not necessarily invertible. Horizontal and vertical mate pasting are further
project/Mathlib results, not a pasting theorem stated by the source.

Import `RingedSpaces` for the public aggregate, or
`RingedSpaces.Modules.BaseChangePasting` for the narrower leaf. Both expose
the **actual** `RingedSpaces.Modules.BaseChange.pushPull` comparison for
arbitrary commutative squares of full ringed-space morphisms. Here `L` is
sheafified coefficient-changing inverse image, `R` is full direct image,
and `A` is their actual adjunction. Their canonical composition isomorphisms
come from `RingedSpaces.Modules.PullbackCoherence`.

* `BaseChange.pushPull_pastePullback` composes squares left to right:

  ```text
  W₀ ─a₀₁→ W₁ ─a₁₂→ W₂
  │v₀       │v₁       │v₂
  Z₀ ─b₀₁→ Z₁ ─b₁₂→ Z₂
  ```

  The result expands `L (b₀₁ ≫ b₁₂)` through `pullbackComp.inv`, applies
  the right square's mate followed by the left square's mate, then contracts
  `L a₁₂ ⋙ L a₀₁` through `pullbackComp.hom`.

* `BaseChange.pushPull_pastePushforward` composes squares top to bottom:

  ```text
  W₀ ─a₀→ X₀
  │v₀      │w₀
  W₁ ─a₁→ X₁
  │v₁      │w₁
  W₂ ─a₂→ X₂
  ```

  The result expands `R (w₀ ≫ w₁)` through `pushforwardComp.inv`, applies
  the lower mate followed by the upper mate, then contracts `R v₀ ⋙ R v₁`
  through `pushforwardComp.hom`.

Both are equalities of natural transformations with explicit functor
associators, not strict identifications of functors. Only the two constituent
square-commutativity equalities are assumed: no Cartesian, flatness, nonzero,
invertibility, or raw-tensor-section condition is required. The proofs use
mathlib's `mateEquiv_vcomp` and `mateEquiv_hcomp` and the existing composition
coherence of the actual functors. The public client
[`RingedSpacesTests/RingedSpaceBaseChangePasting.lean`](../RingedSpacesTests/RingedSpaceBaseChangePasting.lean)
checks both arbitrary-square laws and the non-Cartesian empty-corner example,
using the explicit existing fixture import `RingedSpacesTests.RingedSpaceBaseChange`.

Formal Frontier contributors developed the original pasting proof and clients
and adapted them for this library; see [attribution](../NOTICE.md). This guide
documents the actual available API, not a source-coverage assertion.
