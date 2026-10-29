import Taeyoung.Fisher.GraphonBridge

/-!
# Fisher's triangle-density bound

Atlas 126 and Atlas 148 (and, through it, Atlas 145) need a *sharp*
triangle-density lower bound on their low-density intervals.  For Atlas 148,
`notes/atlas148_paw_bias_hilbert_projection.pdf` bounds the paw density below
by `p·g(p)`, where `g` is the extremal profile of the clique density theorem,
and the required bound is within `3.5%–6%` of `g` on `[1/2, 3/5]`, far too
tight for Goodman's bound, which is `15%–33%` short there.

Fisher's theorem [D. C. Fisher, *Lower bounds on the number of triangles in a
graph*, J. Graph Theory 13 (1989)] is the `k = 2` branch of that profile, on the
band `1/2 < p ≤ 2/3`:

```
t(K₃, W) ≥ (3/2)·c·(1-c)²,      c = (1 - √(4-6p))/3.
```

These proofs need the sharp profile only up to `p = 2/3` (above it Atlas 148
uses Goodman's bound `t(K₃) ≥ p(2p-1)`), so the clique density theorem of
Razborov and Reiher is not needed.

## Files

* the finite theorem: `CliqueCounts`, `DependencePolynomial`, `SmallestRoot`,
  `ThirdTruncation`, `Spectral`, `CubicOpt`, `FiniteTheorem`;
* graphons as integral kernels: `Graphon`, `Kernel`, `Interface`;
* the transfer to graphons: `GraphonContinuity`, `GraphonScaling`,
  `FiniteGraphon`, `GraphonRounding`, `GraphonSampling`, `GraphonBridge`.

The result is

```lean
theorem Taeyoung.Fisher.triangleDensityLowerBound_twoThirds :
    Taeyoung.Fisher.TriangleDensityLowerBoundUpTo.{u} (2 / 3)
```

and `Taeyoung/Methods/TriangleDensity/Fisher.lean` restates it for the bundled
graphons of `Foundation/` (`fisher_triangle_bound`).
-/
