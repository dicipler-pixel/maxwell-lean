# d4 / m4 — Target 5: the divergence theorem on a strictly larger class of regions

**File:** `.ultramath/smwatx3t5/m4/BoxComplex.lean` (714 lines, Lean 4.33.1 + Mathlib 4.33.1,
zero `sorry`, zero non-standard axioms; only propext, Classical.choice, Quot.sound).

## 1. What was open and what is now closed

`Maxwell.Treatise.ElectrostaticStress` proves `art105_directAction` ("the force `ρE` is accounted
for by the stress `p_hk = E_h E_k/4π − δ_hk E²/8π`") on a single box `[a,b]`, because Mathlib has
the divergence theorem only for boxes. Maxwell asks for *any* closed surface (1881, Art. 105,
p. 147). This file extends the class of regions and the class of fields, with **no new analysis** —
everything follows by additivity from Mathlib's
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`.

### 1a. Region class achieved

Let `rowDiv f x = ∑ᵢ ∂ᵢ (f i) x` and `rowFlux f a b` be the signed face flux of the box `[a,b]`
(Maxwell's `boxSurfaceForce` for the stress whose `k`-th column is `f`).

| theorem | region |
|---|---|
| `integral_rowDiv_box` | one box `[a,b]` (Mathlib's theorem, restated) |
| `integral_rowDiv_biUnion` | finite union of boxes with pairwise **null** intersections |
| `integral_rowDiv_sdiff` | `[a,b] \ [c,d]` with `[c,d] ⊆ [a,b]` (inner faces carry the outward normal of `[a,b] \ [c,d]`) |
| `integral_rowDiv_boxComplex` | `(⋃_{B∈O} B) \ (⋃_{B∈H} H)` — polycube with holes, the largest class here |
| `setIntegral_biUnion_boxes` | the pure-integration form: if `∫_B g = Φ B` on each box of a null-intersecting family, `∫_{⋃B} g = ∑ Φ B` |
| `accountedForByStress_biUnion` | the repository's `AccountedForByStress` lifted from boxes to all those box complexes |

Membership is automatic for **touching** boxes: shared faces cancel in `Finset.sum` of
`boxSurfaceForce`, exactly as the physics requires. Nullity of the intersection of touching boxes is
`volume_Icc_inter_Icc_eq_zero` (touching along `x_i = const`; `volume_coord_eq_zero`).

Concrete, fully discharged instance: `art105_staircase` — the staircase
`[0,1]³ ∪ ([1,2]×[1,2]×[0,1])` (two unit cubes glued along an edge), with all hypotheses proved;
`staircase_not_box` proves this region is **not** a box (the point `(1/2,3/2,1/2)` of the
enclosing box is in neither cube). So the class is strictly larger, not merely differently stated.

### 1b. Field class achieved

`IsStressPotentialOn Ψ ρ s` := `Ψ` is `C²` **at each point of `s`**, `∇²Ψ = 4πρ` **on `s`**
(Maxwell's sign), and `ρ` continuous on `s`. The repo's `Art105DirectAction` needs `ContDiff ℝ 2 Ψ`
globally and the Poisson equation globally.

| theorem | statement |
|---|---|
| `art105_box` | on a box: `∫_{[a,b]} ρ E_k = boxSurfaceForce (stress1881 Ψ) a b k`, `E = −∇Ψ` |
| `art105_biUnion` | same over a null-intersecting finite union of boxes |
| `art105_sdiff` | same over a box with a hole |
| `art105_boxComplex` | same over a polycube with holes |
| `art105_sqBox` | concrete: `Ψ = x₀²+x₁²+x₂²`, `ρ = −3/2π` (uses `maxwellNabla2_sq : ∇²(sq) = −6`) |
| `art105_planeKernel_box` | concrete singular case: `Ψ = 1/x₀`, `ρ = −(1/2π)x₀⁻³`; needs only `x₀ ≠ 0` on the box |

The weakening is *strict*: `not_contDiff_planeKernel` proves `1/x₀` is not `C²` on `ℝ³` (not even
continuous at `0`), so `Art105DirectAction` cannot be instantiated with it at all, while
`art105_planeKernel_box` applies to every box avoiding the plane `x₀ = 0`.
`maxwellNabla2_planeKernel : ∇²(1/x₀) = −2 x₀⁻³`.

## 2. Exact commands

```
cd /workspace/nucleus/work/projects/p-c1e28406062a4279aca922483c0a99ab/repo
# 1. the repo's ElectrostaticStress does not compile under Mathlib 4.33.1 (it is pinned to 4.36);
#    port with two mechanical fixes (import Mathlib.LinearAlgebra.Matrix.DotProduct;
#    `(dotProduct_self_eq_zero).mp h`), nothing else changed:
LEAN_PATH=".:$LEAN_PATH" lean -o .ultramath/smwatx3t5/m4/olean/Maxwell/Basic.olean Maxwell/Basic.lean
LEAN_PATH=".ultramath/smwatx3t5/m4/olean:.:$LEAN_PATH" lean \
  -o .ultramath/smwatx3t5/m4/olean/Maxwell/Treatise/ElectrostaticStress.olean \
  .ultramath/smwatx3t5/m4/port/Maxwell/Treatise/ElectrostaticStress.lean
# 2. the deliverable
LEAN_PATH=".ultramath/smwatx3t5/m4/olean:.:$LEAN_PATH" lean \
  -o .ultramath/smwatx3t5/m4/olean/BoxComplex.olean .ultramath/smwatx3t5/m4/BoxComplex.lean
# 3. axioms
LEAN_PATH=".ultramath/smwatx3t5/m4/olean:.:$LEAN_PATH" lean .ultramath/smwatx3t5/m4/axioms.lean
```

`#print axioms` for all 24 delivered theorems (verbatim, `axioms.out`; every line reads exactly
`[propext, Classical.choice, Quot.sound]`):

```
'Maxwell.integral_rowDiv_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.integral_rowDiv_biUnion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.integral_rowDiv_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.integral_rowDiv_boxComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.setIntegral_biUnion_boxes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.accountedForByStress_biUnion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.art105_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.art105_biUnion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.art105_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.art105_boxComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.volume_Icc_inter_Icc_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.art105_sqBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.art105_staircase' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.staircase_not_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.maxwellNabla2_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.pd_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.maxwellNabla2_planeKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.isStressPotentialOn_planeKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.art105_planeKernel_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.not_contDiff_planeKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.norm_vec3_eq_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.norm_three_four_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.norm_one_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Maxwell.art105_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. A notation trap recorded in the file

`Vec3 = Fin 3 → ℝ` carries Mathlib's `Pi.normedAddCommGroup`, so **`‖·‖` is the sup norm**, not the
Euclidean norm: `norm_vec3_eq_sup (x:Vec3) : ‖x‖ = max (max |x 0| |x 1|) |x 2|`,
`norm_three_four_zero : ‖![3,4,0]‖ = 4` (not 5), `norm_one_one_zero : ‖![1,1,0]‖ = 1` (not √2).
The Newtonian radius of Arts. 616–617 is `√(sq (x−y))`; `1/‖x‖` is *not* harmonic off `0`, so this
matters for any formalisation of the Newtonian potential (it does not matter for decay estimates).

## 4. What is still open, and the exact missing lemma

1. **Curved surfaces.** Maxwell's "any closed surface" is not reached. The missing lemma is a
   divergence theorem for a `C¹` image of a box, i.e.
   `∫_{φ([a,b])} div F = ∫_{∂[a,b]} ⟨F(φ y), cof(Dφ y) · n(y)⟩` for `φ` a `C¹` diffeomorphism of a
   neighbourhood of `[a,b]`: Mathlib 4.33.1 has the change-of-variables formula
   (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`-style for boxes) but no
   **surface** Jacobian (`cof`/adjugate) machinery, and no Stokes theorem for manifolds with
   corners that could be instantiated here. Everything else in this file is region-agnostic: once
   `∫_{φ([a,b])} div = flux φ` is available as a `hbox` hypothesis,
   `setIntegral_biUnion_boxes` and `integral_rowDiv_biUnion` carry it to finite unions and
   `integral_rowDiv_sdiff` to holes without change.
2. **A singularity inside a hole.** `integral_rowDiv_boxComplex` requires the row field to be
   `ContinuousOn` each **closed** box, including the boxes that are removed. So the region
   "box with a hole containing a singularity" is *not* covered: Mathlib's box theorem cannot be
   applied to the outer box when the field blows up inside the hole. This is exactly what the
   singular-integral argument for Art. 616/617 needs (cut a small box out around the singularity and
   let it shrink). Missing lemma: a divergence theorem on the region `[a,b] \ S` for `S` a closed
   null-ish singular set, e.g. for `S` a small box *plus* the limit of the flux through `∂S` as
   `S` shrinks (the `4π` solid-angle term). The `off_countable` version of Mathlib's theorem does
   not help: a spherical shell is not a box.
3. Boxes whose intersection has positive measure are deliberately excluded (`hae`); for those the
   sum of the face fluxes double-counts the common boundary, which is the correct behaviour of the
   surface functional, and the identity `∫_{B₁∪B₂} = Φ₁ + Φ₂ − ∫_{B₁∩B₂}` shows why the
   null-intersection hypothesis is optimal in this formulation.
