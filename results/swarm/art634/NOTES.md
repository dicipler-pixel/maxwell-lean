# Direction d3 — Art. 634 (`Art634KineticEnergy`): Stokes for rectangular circuits, and why the stated equation needs the wire hypothesis

Files (all in `.ultramath/smwatx3t5/m2/src/`):

* `Art634Stokes.lean` — Stokes theorem on planar rectangles and on L-shaped rectilinear
  regions, the curl-free corollary, and the refutation of `Art634KineticEnergy` as stated.
* `Art634Circuits.lean` — the four-leg parametrisation of a rectangular circuit, and that its
  `Maxwell.circuitMomentum` equals the induction flux through the rectangle.
* `Art634ClosedSurface.lean` — the closed-surface companion: `div (curl 𝔄) = 0` (Art. 403 with
  Art. 591) and zero flux of `curl 𝔄` through the boundary of any box.
* `AxiomCheck.lean` — the `#print axioms` audit of all 16 theorems.
* `Maxwell/…` — a **verbatim copy** of the repository's `Maxwell` tree (see "Build" below).

## Results

Stokes (Art. 591 `𝔅 = curl 𝔄` with Art. 590/604 `p = ∮𝔄·ds`), for `𝔄` of class `C¹`:

```
stokes_rect_gen
  ∫_{x∈[a,b]} ∫_{y∈[c,d]} (curl 𝔄)_{k} ∘ φ  =  ((∫_{[a,b]} 𝔄_s(·,c)) + ∫_{[c,d]} 𝔄_t(b,·))
                                               − (∫_{[a,b]} 𝔄_s(·,d)) − ∫_{[c,d]} 𝔄_t(a,·)
```
for any plane embedding `φ` with derivative `L`, `L(1,0) = e_s`, `L(0,1) = e_t`, where
`curl 𝔄_k = ∂_s 𝔄_t − ∂_t 𝔄_s` in the cyclic pair `(s,t) = (k+1,k+2)`.

```
art591_stokes_rect0 / _rect1 / _rect2   -- the three coordinate planes, rectangle [a,b]×[c,d]
art591_stokes_L2                        -- L-shaped region [a,b]×[c,d] ∪ [b,b']×[c',d]:
                                        --   six-sided boundary, shared edge {b}×[c',d] cancels
rectCirc2_eq_zero_of_curl_eq_zero       -- curl 𝔄 = 0 ⇒ circulation 0 (surface can be moved)
```
Class of surfaces achieved: **planar rectangles in any coordinate plane, L-shaped rectilinear
hexagons** (a strict superset of rectangles), and **closed box surfaces**:

```
div_curl_eq_zero            -- Art. 403 (8) with Art. 591: div (curl 𝔄) = 0 for C² 𝔄
boxFlux_curl_eq_zero        -- the flux of curl 𝔄 through the six faces of any box is 0
```
The last is what makes `∮ 𝔄·ds` of a closed circuit independent of the spanning surface (two
spans together bound a closed region), so Art. 590's "the electromagnetic momentum of a circuit"
is well defined.  Not achieved: general `C¹`-images of boxes, general polygonal regions.

Circuit side (Arts. 590–591):
```
circuitMomentum_rectPath2
  circuitMomentum 𝔄 (rectPath2 e a b c d) (rectVel2 e a b c d) = rectFlux2 𝔄 e a b c d
art634_single_circuit
  ½ ∑_{i:Unit} pᵢ iᵢ = ½ · i · (flux of curl 𝔄 through the rectangle)
```
with `rectPath2` the four straight legs `(a,c)→(b,c)→(b,d)→(a,d)→(a,c)` on
`t ∈ [k/4,(k+1)/4]` and `rectVel2` its derivative off the three corners.

## The statement as written is false

`Maxwell.Statements.Art634KineticEnergy` has no hypothesis linking `J` to the circuits `γᵢ`,
so `art634_shape_needs_wire_hypothesis` refutes it: with `𝔄 = e₀` constant, `J = 0`, the open
path `γ t = t e₀` and unit current, the momentum side is `½` and the current-density side is
`0`. A correct Art. 634 needs the wire hypothesis "the loops `γᵢ` carry the current `J`".

## What remains (the precise gap)

`J` in `Art634KineticEnergy` is a *function* `Vec3 → Vec3`, whereas a circuit carries its
current on a curve. The exact identity `∑ iᵢ ∮_{γᵢ} 𝔄 · ds = ∫ 𝔄 · J` therefore requires `J`
to be the distributional sum `∑ iᵢ ∮_{γᵢ} δ`, which is not representable by a function; the
provable version is a thin-wire limit, and needs two things absent from Mathlib 4.33.1:

1. a tubular-neighbourhood construction (a solid torus around a `C¹` embedded circle `γ`, with
   cross-section `πε²` and current density `i/(πε²)` tangential along `γ`), and
2. the dominated-convergence limit `∫ 𝔄 · J_ε → i ∮_γ 𝔄 · ds` as `ε → 0`.

Nothing of that kind exists in Mathlib 4.33.1 (no tubular neighbourhood theorem, no
`Measure`-valued currents). The field side — the half that only involves `𝔄` — is closed above.

## Build (one-line repo fix needed)

The repository does **not** compile on Lean 4.33.1 as it stands:
`Maxwell/Treatise/ElectrostaticStress.lean` uses `Matrix.dotProduct_self_eq_zero`, which
4.33.1's import graph does not reach; adding `import Mathlib.LinearAlgebra.Matrix.DotProduct`
to that file makes the whole tree compile. Since no repository file may be modified, the copy
in `src/Maxwell/` is verbatim except for that one added import, so that the theorems below
speak about the repository's own `Maxwell.circuitMomentum` and
`Maxwell.Statements.Art634KineticEnergy`.

```
cd <repo>/.ultramath/smwatx3t5/m2/src
export LEAN_PATH="$PWD:$LEAN_PATH"
for m in Maxwell.Basic Maxwell.Sources Maxwell.Treatise.ElectrostaticStress \
         Maxwell.Treatise.MagneticStress Maxwell.Treatise.Energy \
         Maxwell.Treatise.RadiationPressure Maxwell.Treatise.VectorPotential \
         Maxwell.Treatise.ElectromotiveForce Maxwell.Statements \
         Art634Stokes Art634Circuits Art634ClosedSurface; do
  p=$(echo $m | tr '.' '/'); lean -o $p.olean -i $p.ilean $p.lean
done
lean AxiomCheck.lean
```

`#print axioms` on all 16 theorems: `propext, Classical.choice, Quot.sound` only.

## Numerical check of the conventions (sympy, `.scratch/check.py`)

With `𝔄 = (xy + sin xy, x²z + y³, xz² + eˣy)`, `e = 1/2`, `[a,b] = [0,1]`, `[c,d] = [0,2]`,
`[b,b'] = [1,2]`, `[c',d] = [1,2]`:

* flux through the rectangle `= cos 2 / 2 − 1/2 =` circulation;
* flux through the L-shaped region `= cos 4/2 − cos 2 + cos 1 − 1/2 =` its six-side circulation;
* the four-leg momentum integral equals both;
* for the box `[0,1]×[0,2]×[0,3]` the six face fluxes of `curl 𝔄` are `6e−6`, `−6e−3`, `cos2/2+9/2`,
  `−3/2+cos2/2`, `6`, `−9` (all nonzero) and their outward sum is `0`.

So the orientation conventions in the Lean statements are right, and the statements are not
vacuous (the field is neither curl-free nor a gradient).
