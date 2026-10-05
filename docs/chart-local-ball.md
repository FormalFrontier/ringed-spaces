# Chart coordinates and smooth scalar functions on an entire ball

Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
draft), Definition 4.3.9 (p. 142), motivates smooth scalar-function local
models on entire balls. The indexed boundaryless chart geometry and canonical
whole smooth scalar locally ringed-space comparison here are project and
Mathlib constructions, not arbitrary-sheaf recovery or a printed proof in
that definition.

For a nontrivially normed field `𝕜 : Type u`, a normed space `E : Type v` over
`𝕜`, a charted space `M : Type w` modeled on `E`, and
`[IsManifold 𝓘(𝕜, E) n M]`,
[`ChartedSpace.chartLocalBall n x`](../RingedSpaces/ChartedSpace/LocalBall.lean)
constructs `ChartLocalBall n x` for every `x : M` and every `n : ℕ∞ω`.
Its open `neighborhood` contains `x` and lies inside `(chartAt E x).source`.
Its `radius` is strictly positive, and `coord` is an `n`-diffeomorphism onto
the **entire** open ball `chartBall x radius` centered at `(chartAt E x) x`.
The equations `coord_apply` and `coord_symm_apply` identify both coordinate
maps with the chosen chart and its inverse. The `ball`, `mem_ball`,
`center_mem_ball`, `center`, and `coord_at_center` API provides its center and
membership laws. No finite-dimensionality, completeness, separation,
positive dimension, or nonempty-carrier assumption is needed. A general
model with corners may have no ambient ball at a boundary point.

The existing [`FiniteRegularityFunctions.localBall r x`](finite-regularity-functions.md#finite-order-local-balls)
packages this same indexed construction at `n = (r : ℕ∞ω)`, retaining the
finite-order `LocalBall` fields and its scalar-function locally ringed-space
isomorphism. It does not choose a second radius.

For `n = ∞`, the
[`ChartLocalBall.smoothIso`](../RingedSpaces/ChartedSpace/SmoothLocalBall.lean)
compares the **restriction of the ambient canonical smooth scalar locally
ringed space** to `neighborhood` with the canonical smooth scalar locally
ringed space on the entire coordinate ball. The whole-arrow laws
`smoothIso_hom` and `smoothIso_inv` express the two directions using Mathlib's
restriction isomorphism and smooth chart maps; `restrict_smoothIso_hom`
recovers the intrinsic chart arrow. The three base-map lemmas identify the
point maps. `smoothIso_hom_germ_eval` evaluates a pulled-back germ at the
chart image, and `smoothIso_hom_section_germ_eval` does the same for a
pulled-back section regarded as a germ through the **full composite**.

The [ordinary-root examples](../RingedSpacesTests/ChartedSpaceSmoothLocalBall.lean)
use a proper real interval and a nonconstant section `q ↦ q + 2` to evaluate
both composites to `2`; a zero-dimensional model has a constant-section
evaluation of `4`, and an empty carrier has no chosen point. The smooth
locally ringed-space API uses one Lean universe for the scalar, model and
carrier types because Mathlib's smooth sheaf does; the chart geometry above
has three independent universes. Smooth regularity `∞` is distinct from
analytic regularity `ω`. This canonical scalar comparison gives no converse
for arbitrary sheaves, no chart independence or corners result, and no claim
about merely differentiable or holomorphic functions. A real specialization
requiring a Hausdorff, second-countable manifold has additional assumptions
not needed for the generic chart-ball geometry.
