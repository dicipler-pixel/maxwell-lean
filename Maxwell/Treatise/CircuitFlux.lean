/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.VectorPotential
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Circulation and flux: Stokes on rectangles (Treatise 1873, vol. II, Arts. 590–591, 634)

Art. 591 equations (A) write the magnetic induction as `𝔅 = curl 𝔄` of the electromagnetic momentum
`𝔄`, and Arts. 590 and 604 make the momentum of a circuit its line integral `∮ 𝔄 · ds`. The step
that converts one into the other — the field-side half of Art. 634 eq. (16),
`T = ½ ∑ pᵢ iᵢ = ½ ∭ 𝔄 · C` — is Stokes' theorem on a surface spanning the circuit.

What Mathlib supports here is the rectangle: Green's theorem on `[a,b] × [c,d]`
(`integral2_divergence_prod_of_hasFDerivAt`). `stokes_rect_gen` gives the circulation as the flux
of the matching curl component for a plane embedding of a rectangle with the right tangent frame;
`art591_stokes_rect0/1/2` discharge the curl identification in the three coordinate planes;
`art591_stokes_L2` extends the region to an L-shaped hexagon; `rectCirc2_eq_zero_of_curl_eq_zero`
is the corollary for induction-free fields. `circuitMomentum_rectPath2` evaluates the repository's
`circuitMomentum` on the four straight legs of a rectangle and gets exactly the flux, which is
`art634_single_circuit`.

Closed surfaces: `div_curl_eq_zero` is Art. 403 (8) with Art. 591, and `boxFlux_curl_eq_zero` says
the induction flux through the six faces of a box vanishes. With them the momentum of a closed
circuit is independent of the surface spanning it, which is what Art. 590's phrase "the
electromagnetic momentum of a circuit" presupposes.

Not covered: curved spanning surfaces (no surface measure or manifold Stokes theorem is used), and
the current side of Art. 634 — a circuit's current lives on a curve, not on a density
`J : Vec3 → Vec3`, so `½ ∑ pᵢ iᵢ = ½ ∫ 𝔄 · J` needs a distributional current or a thin-wire limit.
`Maxwell.Statements.art634_shape_needs_wire_hypothesis` refutes the equation without that link.
-/

namespace Maxwell

open Matrix MeasureTheory
open scoped Interval

/-
Copyright (c) 2026. Released under the MIT license (see LICENSE).
-/

/-!
# Art. 634: Stokes' circulation identity for rectangular circuits

Treatise 1873, vol. II, Art. 634, eq. (16) (p. 248) writes the kinetic energy of the currents as
`T = ½ ∑ pᵢ iᵢ = ½ ∭ (Fu + Gv + Hw)`, with `pᵢ = ∮ 𝔄 · ds` the electromagnetic momentum of
circuit `i` (`Maxwell.circuitMomentum`, Arts. 590, 604) and `𝔄` the vector potential.

The two sides of `Maxwell.Statements.Art634KineticEnergy` are integrals over different objects:
a finite sum of line integrals over loops `γᵢ`, and a volume integral against a current density
`J : Vec3 → Vec3`.  The step that lets one be converted into the other is Stokes' theorem on a
surface spanning each circuit.  This file proves that step for the class of surfaces Mathlib
4.33.1 supports exactly — planar rectangles in a coordinate plane — with the normal of the
right-handed cyclic orientation:

`∮_{∂R} 𝔄 · ds = ∫_R (curl 𝔄) · n dS`.

So (Art. 591, `𝔅 = curl 𝔄`) the momentum of a rectangular circuit is the induction flux through
it, which is the field-side half of Art. 634.
-/



/-! ## The three coordinate planes, with right-handed surface coordinates

For the plane `x_k = e` the surface coordinates `(s, t)` are chosen cyclically,
`(s, t) = (k+1, k+2)` mod 3, so that `e_s × e_t = e_k`, and the flux integral of the `k`-th
component of the curl equals the circulation in the positive sense about `e_k`. -/

/-- The linear map `(s, t) ↦ s • e_s + t • e_t`, used as the derivative of each plane embedding. -/
noncomputable def planeCoord (s t : Fin 3) : (ℝ × ℝ) →L[ℝ] Vec3 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (axis s) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (axis t)

theorem planeCoord_apply (s t : Fin 3) (q : ℝ × ℝ) :
    planeCoord s t q = q.1 • axis s + q.2 • axis t := rfl

@[simp] theorem planeCoord_one_zero (s t : Fin 3) : planeCoord s t (1, 0) = axis s := by
  rw [planeCoord_apply]; simp

@[simp] theorem planeCoord_zero_one (s t : Fin 3) : planeCoord s t (0, 1) = axis t := by
  rw [planeCoord_apply]; simp

/-- The point of the plane `x₀ = e` with surface coordinates `(x₁, x₂) = (s, t)`. -/
noncomputable def pt0 (e : ℝ) (q : ℝ × ℝ) : Vec3 := q.1 • axis 1 + q.2 • axis 2 + e • axis 0

/-- The point of the plane `x₁ = e` with surface coordinates `(x₂, x₀) = (s, t)`. -/
noncomputable def pt1 (e : ℝ) (q : ℝ × ℝ) : Vec3 := q.1 • axis 2 + q.2 • axis 0 + e • axis 1

/-- The point of the plane `x₂ = e` with surface coordinates `(x₀, x₁) = (s, t)`. -/
noncomputable def pt2 (e : ℝ) (q : ℝ × ℝ) : Vec3 := q.1 • axis 0 + q.2 • axis 1 + e • axis 2

theorem hasFDerivAt_pt0 (e : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (pt0 e) (planeCoord 1 2) p := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => planeCoord 1 2 q + e • axis 0)
      (planeCoord 1 2) p := (planeCoord 1 2).hasFDerivAt.add_const _
  simpa [pt0, planeCoord_apply] using h

theorem hasFDerivAt_pt1 (e : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (pt1 e) (planeCoord 2 0) p := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => planeCoord 2 0 q + e • axis 1)
      (planeCoord 2 0) p := (planeCoord 2 0).hasFDerivAt.add_const _
  simpa [pt1, planeCoord_apply] using h

theorem hasFDerivAt_pt2 (e : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (pt2 e) (planeCoord 0 1) p := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => planeCoord 0 1 q + e • axis 2)
      (planeCoord 0 1) p := (planeCoord 0 1).hasFDerivAt.add_const _
  simpa [pt2, planeCoord_apply] using h

theorem continuous_pt0 (e : ℝ) : Continuous (pt0 e) :=
  (planeCoord 1 2).continuous.add continuous_const

theorem continuous_pt1 (e : ℝ) : Continuous (pt1 e) :=
  (planeCoord 2 0).continuous.add continuous_const

theorem continuous_pt2 (e : ℝ) : Continuous (pt2 e) :=
  (planeCoord 0 1).continuous.add continuous_const

/-! ## Surface and circuit integrals for a rectangle -/

/-- Flux of the induction `𝔅 = curl 𝔄` through the rectangle `[a,b] × [c,d]` of the plane
`x₂ = e`, with normal `+e₂`. -/
noncomputable def rectFlux2 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, curl A (pt2 e (x, y)) 2

/-- Circulation of `𝔄` round the boundary of the same rectangle, taken counterclockwise seen
from `+e₂`: `(a,c) → (b,c) → (b,d) → (a,d) → (a,c)`. -/
noncomputable def rectCirc2 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  (∫ x in a..b, A (pt2 e (x, c)) 0) + (∫ y in c..d, A (pt2 e (b, y)) 1) -
    (∫ x in a..b, A (pt2 e (x, d)) 0) - (∫ y in c..d, A (pt2 e (a, y)) 1)

/-- Flux of `𝔅` through the rectangle `[a,b] × [c,d]` (in `(x₂, x₀)`) of the plane `x₁ = e`,
with normal `+e₁`. -/
noncomputable def rectFlux1 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, curl A (pt1 e (x, y)) 1

/-- Circulation round the same rectangle, counterclockwise seen from `+e₁`. -/
noncomputable def rectCirc1 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  (∫ x in a..b, A (pt1 e (x, c)) 2) + (∫ y in c..d, A (pt1 e (b, y)) 0) -
    (∫ x in a..b, A (pt1 e (x, d)) 2) - (∫ y in c..d, A (pt1 e (a, y)) 0)

/-- Flux of `𝔅` through the rectangle `[a,b] × [c,d]` (in `(x₀, x₁)`) of the plane `x₀ = e`,
with normal `+e₀`. -/
noncomputable def rectFlux0 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, curl A (pt0 e (x, y)) 0

/-- Circulation round the same rectangle, counterclockwise seen from `+e₀`. -/
noncomputable def rectCirc0 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  (∫ x in a..b, A (pt0 e (x, c)) 1) + (∫ y in c..d, A (pt0 e (b, y)) 2) -
    (∫ x in a..b, A (pt0 e (x, d)) 1) - (∫ y in c..d, A (pt0 e (a, y)) 2)

/-! ## The generic rectangle theorem -/

/-- **Stokes for a coordinate rectangle.**  For a plane embedding `φ` with derivative `L`, an axis
`k` whose curl component is `∂_s 𝔄_t − ∂_t 𝔄_s` in the cyclic pair `(s,t)`, with `L (1,0) = e_s`
and `L (0,1) = e_t`, the flux of `curl 𝔄` through the rectangle equals the circulation round its
boundary.  This is `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt` (Green's theorem on
`[a,b] × [c,d]`) applied to the components `(𝔄_t, −𝔄_s)`. -/
theorem stokes_rect_gen {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A)
    {s t k : Fin 3} {φ : ℝ × ℝ → Vec3} {L : (ℝ × ℝ) →L[ℝ] Vec3}
    (hφc : Continuous φ) (hφd : ∀ p, HasFDerivAt φ L p)
    (hL₀ : L (1, 0) = axis s) (hL₁ : L (0, 1) = axis t)
    (hcurl : ∀ x, curl A x k = pd s (fun z => A z t) x - pd t (fun z => A z s) x)
    (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, curl A (φ (x, y)) k) =
      (((∫ x in a..b, -(A (φ (x, d)) s)) - ∫ x in a..b, -(A (φ (x, c)) s)) +
          ∫ y in c..d, A (φ (b, y)) t) -
        ∫ y in c..d, A (φ (a, y)) t := by
  have hdt : Differentiable ℝ (fun z => A z t) :=
    (contDiff_pi.1 hA t).differentiable (by norm_num)
  have hds : Differentiable ℝ (fun z => A z s) :=
    (contDiff_pi.1 hA s).differentiable (by norm_num)
  have Hdf : ∀ p ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min c d) (max c d),
      HasFDerivAt (fun p : ℝ × ℝ => A (φ p) t)
        ((fderiv ℝ (fun z => A z t) (φ p)).comp L) p := by
    intro p _
    have h := (hdt (φ p)).hasFDerivAt.comp p (hφd p)
    simpa [Function.comp_def] using h
  have Hdg : ∀ p ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min c d) (max c d),
      HasFDerivAt (-(fun p : ℝ × ℝ => A (φ p) s))
        (-((fderiv ℝ (fun z => A z s) (φ p)).comp L)) p := by
    intro p _
    have h := (hds (φ p)).hasFDerivAt.comp p (hφd p)
    exact h.neg
  have hcomp : ∀ p : ℝ × ℝ,
      ((fderiv ℝ (fun z => A z t) (φ p)).comp L) (1, 0) +
          (-((fderiv ℝ (fun z => A z s) (φ p)).comp L)) (0, 1) = curl A (φ p) k := by
    intro p
    rw [hcurl]
    simp [ContinuousLinearMap.comp_apply, hL₀, hL₁, pd]
    ring
  have HcF : ContinuousOn (fun p : ℝ × ℝ => A (φ p) t) ([[a, b]] ×ˢ [[c, d]]) :=
    ((contDiff_pi.1 hA t).continuous.comp hφc).continuousOn
  have HcG : ContinuousOn (-(fun p : ℝ × ℝ => A (φ p) s)) ([[a, b]] ×ˢ [[c, d]]) :=
    ((contDiff_pi.1 hA s).continuous.comp hφc).neg.continuousOn
  have Hi : IntegrableOn (fun p : ℝ × ℝ =>
      ((fderiv ℝ (fun z => A z t) (φ p)).comp L) (1, 0) +
        (-((fderiv ℝ (fun z => A z s) (φ p)).comp L)) (0, 1))
      ([[a, b]] ×ˢ [[c, d]]) := by
    have heq : (fun p : ℝ × ℝ =>
        ((fderiv ℝ (fun z => A z t) (φ p)).comp L) (1, 0) +
          (-((fderiv ℝ (fun z => A z s) (φ p)).comp L)) (0, 1)) =
        fun p => curl A (φ p) k := funext hcomp
    rw [heq]
    exact ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
      (((continuous_apply k).comp ((continuous_curl hA).comp hφc)).continuousOn)
  have key := integral2_divergence_prod_of_hasFDerivAt (fun p : ℝ × ℝ => A (φ p) t)
    (-(fun p : ℝ × ℝ => A (φ p) s)) (fun p => (fderiv ℝ (fun z => A z t) (φ p)).comp L)
    (fun p => -((fderiv ℝ (fun z => A z s) (φ p)).comp L)) a c b d HcF HcG Hdf Hdg Hi
  have hflux : (∫ x in a..b, ∫ y in c..d, curl A (φ (x, y)) k) =
      ∫ x in a..b, ∫ y in c..d,
        ((fun p : ℝ × ℝ => (fderiv ℝ (fun z => A z t) (φ p)).comp L) (x, y)) (1, 0) +
          ((fun p : ℝ × ℝ => -((fderiv ℝ (fun z => A z s) (φ p)).comp L)) (x, y)) (0, 1) := by
    refine intervalIntegral.integral_congr fun x _ =>
      intervalIntegral.integral_congr fun y _ => (hcomp (x, y)).symm
  rw [hflux, key]
  simp only [Pi.neg_apply, intervalIntegral.integral_neg]

/-! ## The three planes -/

/-- `curl 𝔄` component `2`, in the cyclic pair `(0,1)`. -/
theorem curl_two (A : Vec3 → Vec3) (x : Vec3) :
    curl A x 2 = pd 0 (fun z => A z 1) x - pd 1 (fun z => A z 0) x := by
  simp [curl]

/-- `curl 𝔄` component `1`, in the cyclic pair `(2,0)`. -/
theorem curl_one (A : Vec3 → Vec3) (x : Vec3) :
    curl A x 1 = pd 2 (fun z => A z 0) x - pd 0 (fun z => A z 2) x := by
  simp [curl]

/-- `curl 𝔄` component `0`, in the cyclic pair `(1,2)`. -/
theorem curl_zero (A : Vec3 → Vec3) (x : Vec3) :
    curl A x 0 = pd 1 (fun z => A z 2) x - pd 2 (fun z => A z 1) x := by
  simp [curl]

/-- **Art. 591 with Stokes, plane `x₂ = e`.**  The flux of the induction through a rectangle in a
coordinate plane equals the circulation of the momentum round its boundary. -/
theorem art591_stokes_rect2 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ) :
    rectFlux2 A e a b c d = rectCirc2 A e a b c d := by
  simp only [rectFlux2, rectCirc2]
  rw [stokes_rect_gen (A := A) hA (s := 0) (t := 1) (k := 2)
    (φ := pt2 e) (L := planeCoord 0 1) (continuous_pt2 e) (hasFDerivAt_pt2 e)
    (planeCoord_one_zero 0 1) (planeCoord_zero_one 0 1) (curl_two A) a b c d]
  simp only [intervalIntegral.integral_neg]
  ring

/-- **Art. 591 with Stokes, plane `x₁ = e`.** -/
theorem art591_stokes_rect1 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ) :
    rectFlux1 A e a b c d = rectCirc1 A e a b c d := by
  simp only [rectFlux1, rectCirc1]
  rw [stokes_rect_gen (A := A) hA (s := 2) (t := 0) (k := 1)
    (φ := pt1 e) (L := planeCoord 2 0) (continuous_pt1 e) (hasFDerivAt_pt1 e)
    (planeCoord_one_zero 2 0) (planeCoord_zero_one 2 0) (curl_one A) a b c d]
  simp only [intervalIntegral.integral_neg]
  ring

/-- **Art. 591 with Stokes, plane `x₀ = e`.** -/
theorem art591_stokes_rect0 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ) :
    rectFlux0 A e a b c d = rectCirc0 A e a b c d := by
  simp only [rectFlux0, rectCirc0]
  rw [stokes_rect_gen (A := A) hA (s := 1) (t := 2) (k := 0)
    (φ := pt0 e) (L := planeCoord 1 2) (continuous_pt0 e) (hasFDerivAt_pt0 e)
    (planeCoord_one_zero 1 2) (planeCoord_zero_one 1 2) (curl_zero A) a b c d]
  simp only [intervalIntegral.integral_neg]
  ring


/-! ## A strictly larger class: L-shaped rectilinear regions

Two rectangles sharing part of a side: with `a ≤ b ≤ b'` and `c ≤ c' ≤ d` the region
`[a,b]×[c,d] ∪ [b,b']×[c',d]` (in the plane `x₂ = e`) is an L-shaped hexagon, not a rectangle.
Its boundary traverses six segments; the vertical segment `{b} × [c',d]` appears in the two
rectangle boundaries with opposite signs and cancels, which is the whole content of passing from
single rectangles to rectilinear polygonal regions. -/

/-- Circulation round the boundary of the L-shaped region `[a,b]×[c,d] ∪ [b,b']×[c',d]` in the
plane `x₂ = e`, oriented counterclockwise seen from `+e₂`: six side integrals. -/
noncomputable def lCirc2 (A : Vec3 → Vec3) (e a b b' c c' d : ℝ) : ℝ :=
  (∫ x in a..b, A (pt2 e (x, c)) 0) + (∫ y in c..c', A (pt2 e (b, y)) 1) +
      (∫ x in b..b', A (pt2 e (x, c')) 0) + (∫ y in c'..d, A (pt2 e (b', y)) 1) -
    (∫ x in a..b', A (pt2 e (x, d)) 0) - (∫ y in c..d, A (pt2 e (a, y)) 1)

/-- Flux of the induction through the same L-shaped region, as the sum of the two rectangles. -/
noncomputable def lFlux2 (A : Vec3 → Vec3) (e a b b' c c' d : ℝ) : ℝ :=
  rectFlux2 A e a b c d + rectFlux2 A e b b' c' d

/-- **Art. 591 with Stokes, L-shaped regions.**  The flux of the induction through an L-shaped
region equals the circulation of the momentum round its six-sided boundary.  Proof: Stokes on each
of the two rectangles (`art591_stokes_rect2`), additivity of the integral over adjacent intervals
on the two cut sides, and cancellation of the shared segment `{b} × [c',d]`. The identity needs no order on the six scalars: interval integrals are oriented, so it holds for
any `a, b, b', c, c', d`; the ordering `a ≤ b ≤ b'`, `c ≤ c' ≤ d` is what makes it a statement
about an L-shaped region. -/
theorem art591_stokes_L2 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b b' c c' d : ℝ) :
    lFlux2 A e a b b' c c' d = lCirc2 A e a b b' c c' d := by
  have hcontA : Continuous A := hA.continuous
  have h1 : Continuous fun y : ℝ => A (pt2 e (b, y)) 1 := by
    have hp : Continuous fun y : ℝ => pt2 e (b, y) :=
      (continuous_pt2 e).comp (by continuity : Continuous fun y : ℝ => (b, y))
    exact (continuous_apply 1).comp (hcontA.comp hp)
  have h2 : Continuous fun x : ℝ => A (pt2 e (x, d)) 0 := by
    have hp : Continuous fun x : ℝ => pt2 e (x, d) :=
      (continuous_pt2 e).comp (by continuity : Continuous fun x : ℝ => (x, d))
    exact (continuous_apply 0).comp (hcontA.comp hp)
  have hadd1 : (∫ y in c..d, A (pt2 e (b, y)) 1) =
      (∫ y in c..c', A (pt2 e (b, y)) 1) + (∫ y in c'..d, A (pt2 e (b, y)) 1) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (h1.intervalIntegrable c c')
      (h1.intervalIntegrable c' d)]
  have hadd2 : (∫ x in a..b', A (pt2 e (x, d)) 0) =
      (∫ x in a..b, A (pt2 e (x, d)) 0) + (∫ x in b..b', A (pt2 e (x, d)) 0) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (h2.intervalIntegrable a b)
      (h2.intervalIntegrable b b')]
  simp only [lFlux2, lCirc2, rectFlux2]
  rw [show (∫ x in a..b, ∫ y in c..d, curl A (pt2 e (x, y)) 2) = rectCirc2 A e a b c d from
      art591_stokes_rect2 hA e a b c d,
    show (∫ x in b..b', ∫ y in c'..d, curl A (pt2 e (x, y)) 2) = rectCirc2 A e b b' c' d from
      art591_stokes_rect2 hA e b b' c' d]
  simp only [rectCirc2]
  rw [hadd1, hadd2]
  ring

/-! ## Corollary: a curl-free momentum has zero circulation (independence of the surface) -/

/-- If `curl 𝔄 = 0` (everywhere, in particular on the rectangle), the circulation round a
rectangular circuit vanishes: the momentum has no circulation, so the spanning surface can be
moved without changing `∮ 𝔄 · ds`.  This is Art. 598/616's "the added terms disappear" in the
field language. -/
theorem rectCirc2_eq_zero_of_curl_eq_zero {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ)
    (hcurl : ∀ x, curl A x = 0) : rectCirc2 A e a b c d = 0 := by
  rw [← art591_stokes_rect2 hA e a b c d]
  simp only [rectFlux2]
  simp only [hcurl]
  simp

/-
Copyright (c) 2026. Released under the MIT license (see LICENSE).
-/

/-!
# Art. 634: the momentum of a rectangular circuit is the flux of the induction

Treatise 1873, vol. II, Arts. 590 and 604 define the electromagnetic momentum of a circuit as the
line integral of `𝔄` round it (`Maxwell.circuitMomentum`), and Art. 591 sets `𝔅 = curl 𝔄`.  Here
the boundary of a rectangle is given an explicit parametrisation `rectPath2` with velocity
`rectVel2` (four straight legs, the `k`-th leg on `t ∈ [k/4, (k+1)/4]`), and it is proved that the
momentum so obtained is the circulation of `Art634Stokes`, hence, by `art591_stokes_rect2`, the
flux of the induction through the rectangle.

Nothing here is new physics: it identifies the two sides of Art. 634 that talk about `𝔄`, leaving
out exactly the step from circuits to a current density `J`.
-/



attribute [fun_prop] continuous_pt0 continuous_pt1 continuous_pt2

/-- The boundary of the rectangle `[a,b] × [c,d]` of the plane `x₂ = e`, traversed
counterclockwise seen from `+e₂` at unit parameter speed on each of the four legs.  Each branch is
written as the affine map `d₀ + c₀ t` that `intervalIntegral.smul_integral_comp_add_mul` consumes;
the corners are at `t = 1/4, 1/2, 3/4`:
`(a,c) → (b,c) → (b,d) → (a,d) → (a,c)`. -/
noncomputable def rectPath2 (e a b c d : ℝ) (t : ℝ) : Vec3 :=
  if t ≤ 1 / 4 then pt2 e (a + (4 * (b - a)) * t, c)
  else if t ≤ 1 / 2 then pt2 e (b, (2 * c - d) + (4 * (d - c)) * t)
  else if t ≤ 3 / 4 then pt2 e ((3 * b - 2 * a) + (-(4 * (b - a))) * t, d)
  else pt2 e (a, (4 * d - 3 * c) + (-(4 * (d - c))) * t)

/-- The velocity of `rectPath2`; it equals the derivative of `rectPath2` off the three corners and
does not depend on the plane offset `e`. -/
noncomputable def rectVel2 (_e a b c d : ℝ) (t : ℝ) : Vec3 :=
  if t ≤ 1 / 4 then (4 * (b - a)) • axis 0
  else if t ≤ 1 / 2 then (4 * (d - c)) • axis 1
  else if t ≤ 3 / 4 then (-(4 * (b - a))) • axis 0
  else (-(4 * (d - c))) • axis 1

theorem dotProduct_smul_axis0 (v : Vec3) (s : ℝ) : v ⬝ᵥ (s • axis 0) = s * v 0 := by
  rw [dotProduct_smul]
  simp [axis, dotProduct, Fin.sum_univ_three]

theorem dotProduct_smul_axis1 (v : Vec3) (s : ℝ) : v ⬝ᵥ (s • axis 1) = s * v 1 := by
  rw [dotProduct_smul]
  simp [axis, dotProduct, Fin.sum_univ_three]

/-! ### The four legs: the integrand on the open leg, and its value by substitution -/

theorem leg1_fun {A : Vec3 → Vec3} (e a b c d : ℝ) :
    (Set.uIoo (0 : ℝ) (1 / 4)).EqOn
      (fun t => A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t)
      (fun t => (4 * (b - a)) * A (pt2 e (a + (4 * (b - a)) * t, c)) 0) := by
  intro t ht
  simp only [Set.uIoo_of_le (by norm_num : (0:ℝ) ≤ 1 / 4)] at ht
  have ht' : t ≤ 1 / 4 := le_of_lt ht.2
  simp only [rectPath2, rectVel2, if_pos ht']
  rw [dotProduct_smul_axis0]

theorem leg2_fun {A : Vec3 → Vec3} (e a b c d : ℝ) :
    (Set.uIoo (1 / 4 : ℝ) (1 / 2)).EqOn
      (fun t => A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t)
      (fun t => (4 * (d - c)) * A (pt2 e (b, (2 * c - d) + (4 * (d - c)) * t)) 1) := by
  intro t ht
  simp only [Set.uIoo_of_le (by norm_num : (1/4:ℝ) ≤ 1 / 2)] at ht
  have h1 : ¬ t ≤ 1 / 4 := not_le.mpr ht.1
  have h2 : t ≤ 1 / 2 := le_of_lt ht.2
  simp only [rectPath2, rectVel2, if_neg h1, if_pos h2]
  rw [dotProduct_smul_axis1]

theorem leg3_fun {A : Vec3 → Vec3} (e a b c d : ℝ) :
    (Set.uIoo (1 / 2 : ℝ) (3 / 4)).EqOn
      (fun t => A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t)
      (fun t => (-(4 * (b - a))) * A (pt2 e ((3 * b - 2 * a) + (-(4 * (b - a))) * t, d)) 0) := by
  intro t ht
  simp only [Set.uIoo_of_le (by norm_num : (1/2:ℝ) ≤ 3 / 4)] at ht
  have h1 : ¬ t ≤ 1 / 4 := by linarith [ht.1]
  have h2 : ¬ t ≤ 1 / 2 := not_le.mpr ht.1
  have h3 : t ≤ 3 / 4 := le_of_lt ht.2
  simp only [rectPath2, rectVel2, if_neg h1, if_neg h2, if_pos h3]
  rw [dotProduct_smul_axis0]

theorem leg4_fun {A : Vec3 → Vec3} (e a b c d : ℝ) :
    (Set.uIoo (3 / 4 : ℝ) 1).EqOn
      (fun t => A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t)
      (fun t => (-(4 * (d - c))) * A (pt2 e (a, (4 * d - 3 * c) + (-(4 * (d - c))) * t)) 1) := by
  intro t ht
  simp only [Set.uIoo_of_le (by norm_num : (3/4:ℝ) ≤ 1)] at ht
  have h1 : ¬ t ≤ 1 / 4 := by linarith [ht.1]
  have h2 : ¬ t ≤ 1 / 2 := by linarith [ht.1]
  have h3 : ¬ t ≤ 3 / 4 := not_le.mpr ht.1
  simp only [rectPath2, rectVel2, if_neg h1, if_neg h2, if_neg h3]
  rw [dotProduct_smul_axis1]

theorem momentum_leg1 {A : Vec3 → Vec3} (e a b c d : ℝ) :
    (∫ t in (0 : ℝ)..(1 / 4), A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t) =
      ∫ x in a..b, A (pt2 e (x, c)) 0 := by
  rw [intervalIntegral.integral_congr_uIoo (leg1_fun (A := A) e a b c d)]
  have h := intervalIntegral.smul_integral_comp_add_mul (f := fun u => A (pt2 e (u, c)) 0)
    (a := (0 : ℝ)) (b := (1 / 4)) (4 * (b - a)) a
  simp only [smul_eq_mul] at h
  rw [intervalIntegral.integral_const_mul, h]
  rw [show a + 4 * (b - a) * 0 = a by ring, show a + 4 * (b - a) * (1 / 4) = b by ring]

theorem momentum_leg2 {A : Vec3 → Vec3} (e a b c d : ℝ) :
    (∫ t in (1 / 4 : ℝ)..(1 / 2), A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t) =
      ∫ y in c..d, A (pt2 e (b, y)) 1 := by
  rw [intervalIntegral.integral_congr_uIoo (leg2_fun (A := A) e a b c d)]
  have h := intervalIntegral.smul_integral_comp_add_mul (f := fun u => A (pt2 e (b, u)) 1)
    (a := (1 / 4 : ℝ)) (b := (1 / 2)) (4 * (d - c)) (2 * c - d)
  simp only [smul_eq_mul] at h
  rw [intervalIntegral.integral_const_mul, h]
  rw [show 2 * c - d + 4 * (d - c) * (1 / 4) = c by ring,
    show 2 * c - d + 4 * (d - c) * (1 / 2) = d by ring]

theorem momentum_leg3 {A : Vec3 → Vec3} (e a b c d : ℝ) :
    (∫ t in (1 / 2 : ℝ)..(3 / 4), A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t) =
      ∫ x in b..a, A (pt2 e (x, d)) 0 := by
  rw [intervalIntegral.integral_congr_uIoo (leg3_fun (A := A) e a b c d)]
  have h := intervalIntegral.smul_integral_comp_add_mul (f := fun u => A (pt2 e (u, d)) 0)
    (a := (1 / 2 : ℝ)) (b := (3 / 4)) (-(4 * (b - a))) (3 * b - 2 * a)
  simp only [smul_eq_mul] at h
  rw [intervalIntegral.integral_const_mul, h]
  rw [show 3 * b - 2 * a + -(4 * (b - a)) * (1 / 2) = b by ring,
    show 3 * b - 2 * a + -(4 * (b - a)) * (3 / 4) = a by ring]

theorem momentum_leg4 {A : Vec3 → Vec3} (e a b c d : ℝ) :
    (∫ t in (3 / 4 : ℝ)..1, A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t) =
      ∫ y in d..c, A (pt2 e (a, y)) 1 := by
  rw [intervalIntegral.integral_congr_uIoo (leg4_fun (A := A) e a b c d)]
  have h := intervalIntegral.smul_integral_comp_add_mul (f := fun u => A (pt2 e (a, u)) 1)
    (a := (3 / 4 : ℝ)) (b := 1) (-(4 * (d - c))) (4 * d - 3 * c)
  simp only [smul_eq_mul] at h
  rw [intervalIntegral.integral_const_mul, h]
  rw [show 4 * d - 3 * c + -(4 * (d - c)) * (3 / 4) = d by ring,
    show 4 * d - 3 * c + -(4 * (d - c)) * 1 = c by ring]

/-! ### The momentum of the whole circuit -/

/-- **Art. 634, field side (Arts. 590–591 with Stokes).**  The electromagnetic momentum of the
rectangular circuit `rectPath2` is the circulation `rectCirc2` round the rectangle, i.e. the flux
of the induction `curl 𝔄` through it. -/
theorem circuitMomentum_rectPath2 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ) :
    circuitMomentum A (rectPath2 e a b c d) (rectVel2 e a b c d) = rectFlux2 A e a b c d := by
  have hAc : Continuous A := hA.continuous
  have hc1 : Continuous fun t : ℝ => (4 * (b - a)) * A (pt2 e (a + (4 * (b - a)) * t, c)) 0 := by
    fun_prop
  have hc2 : Continuous fun t : ℝ => (4 * (d - c)) * A (pt2 e (b, (2 * c - d) + (4 * (d - c)) * t)) 1
    := by fun_prop
  have hc3 : Continuous fun t : ℝ =>
      (-(4 * (b - a))) * A (pt2 e ((3 * b - 2 * a) + (-(4 * (b - a))) * t, d)) 0 := by fun_prop
  have hc4 : Continuous fun t : ℝ =>
      (-(4 * (d - c))) * A (pt2 e (a, (4 * d - 3 * c) + (-(4 * (d - c))) * t)) 1 := by fun_prop
  set F : ℝ → ℝ := fun t => A (rectPath2 e a b c d t) ⬝ᵥ rectVel2 e a b c d t with hF
  have hi1 : IntervalIntegrable F volume 0 (1 / 4) :=
    (hc1.intervalIntegrable 0 (1 / 4)).congr_uIoo (leg1_fun (A := A) e a b c d).symm
  have hi2 : IntervalIntegrable F volume (1 / 4) (1 / 2) :=
    (hc2.intervalIntegrable (1 / 4) (1 / 2)).congr_uIoo (leg2_fun (A := A) e a b c d).symm
  have hi3 : IntervalIntegrable F volume (1 / 2) (3 / 4) :=
    (hc3.intervalIntegrable (1 / 2) (3 / 4)).congr_uIoo (leg3_fun (A := A) e a b c d).symm
  have hi4 : IntervalIntegrable F volume (3 / 4) 1 :=
    (hc4.intervalIntegrable (3 / 4) 1).congr_uIoo (leg4_fun (A := A) e a b c d).symm
  have h12 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have h123 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  have h1234 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans (hi2.trans hi3)) hi4
  have hsplit : (∫ t in (0 : ℝ)..1, F t) =
      ((∫ t in (0 : ℝ)..(1 / 4), F t) + (∫ t in (1 / 4 : ℝ)..(1 / 2), F t)) +
        (∫ t in (1 / 2 : ℝ)..(3 / 4), F t) + (∫ t in (3 / 4 : ℝ)..1, F t) := by
    rw [← h1234, ← h123, ← h12]
  have hmom : circuitMomentum A (rectPath2 e a b c d) (rectVel2 e a b c d) = rectCirc2 A e a b c d := by
    simp only [circuitMomentum, hF] at *
    rw [hsplit, momentum_leg1, momentum_leg2, momentum_leg3, momentum_leg4]
    simp only [rectCirc2]
    have s1 : (∫ x in b..a, A (pt2 e (x, d)) 0) = -∫ x in a..b, A (pt2 e (x, d)) 0 := by
      conv_lhs => rw [intervalIntegral.integral_symm]
    have s2 : (∫ y in d..c, A (pt2 e (a, y)) 1) = -∫ y in c..d, A (pt2 e (a, y)) 1 := by
      conv_lhs => rw [intervalIntegral.integral_symm]
    rw [s1, s2]
    ring
  rw [hmom, ← art591_stokes_rect2 hA e a b c d]

/-- **Art. 634 for one rectangular circuit, in Maxwell's own shape.**  The energy term
`½ ∑ pᵢ iᵢ` with a single circuit `p = ∮ 𝔄 · ds` is `½ i` times the flux of the induction
`𝔅 = curl 𝔄` through the rectangle: the potential appears only through its curl, exactly as
Art. 635's `½ ∭ 𝔄 · C = (1/8π) ∭ 𝔅 · ℌ` requires. -/
theorem art634_single_circuit {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d i : ℝ) :
    (1 / 2) * (∑ _ : Unit, circuitMomentum A (rectPath2 e a b c d) (rectVel2 e a b c d) * i) =
      (1 / 2) * (i * rectFlux2 A e a b c d) := by
  rw [circuitMomentum_rectPath2 hA e a b c d]
  simp
  ring

/-
Copyright (c) 2026. Released under the MIT license (see LICENSE).
-/

/-!
# Art. 403 with Art. 591: the induction `𝔅 = curl 𝔄` has no magnetic charge

Treatise 1873, vol. II, Art. 591 sets `𝔅 = curl 𝔄`, and Art. 403 (eq. (8), p. 253) is
`div 𝔅 = 0`.  Here:

* `div_curl_eq_zero` — `div (curl 𝔄) = 0` for `𝔄` of class `C²` (a pointwise identity);
* `boxFlux_curl_eq_zero` — the flux of `curl 𝔄` through the closed boundary of any box
  `[a,b]` vanishes, i.e. the mean of the induction over the six faces is zero.

Together with `art591_stokes_rect2` (flux through a rectangle = circulation round it) this is
what makes the electromagnetic momentum `∮ 𝔄 · ds` of a closed circuit independent of which
spanning surface is chosen: two spanning surfaces together bound a closed region, and the flux
through the closed boundary adds to zero.  The class of surfaces here is the closed box surface,
outside the planar rectangles of `Art634Stokes`.
-/



/-- **Art. 403 (eq. (8)) with Art. 591.**  `div (curl 𝔄) = 0` for a `C²` potential: the curl is
solenoidal. -/
theorem div_curl_eq_zero {A : Vec3 → Vec3} (hA : ContDiff ℝ 2 A) (x : Vec3) :
    div (curl A) x = 0 := by
  have h2 : ∀ k, ContDiff ℝ 2 (fun y => A y k) := fun k => contDiff_pi.1 hA k
  have hd : ∀ i k, DifferentiableAt ℝ (fun y => pd i (fun z => A z k) y) x :=
    fun i k => differentiableAt_pd ((h2 k).contDiffAt) i
  have e0 : (fun y => (curl A y) 0) =
      fun y => pd 1 (fun z => A z 2) y - pd 2 (fun z => A z 1) y := by
    funext y; simp [curl]
  have e1 : (fun y => (curl A y) 1) =
      fun y => pd 2 (fun z => A z 0) y - pd 0 (fun z => A z 2) y := by
    funext y; simp [curl]
  have e2 : (fun y => (curl A y) 2) =
      fun y => pd 0 (fun z => A z 1) y - pd 1 (fun z => A z 0) y := by
    funext y; simp [curl]
  simp only [div, Fin.sum_univ_three, e0, e1, e2,
    pd_sub _ (hd 1 2) (hd 2 1), pd_sub _ (hd 2 0) (hd 0 2), pd_sub _ (hd 0 1) (hd 1 0)]
  rw [pd_pd_comm ((h2 2).contDiffAt) (i := 1) (j := 0),
    pd_pd_comm ((h2 1).contDiffAt) (i := 2) (j := 0),
    pd_pd_comm ((h2 0).contDiffAt) (i := 2) (j := 1)]
  ring

/-- `curl 𝔄` is `C¹` when `𝔄` is `C²`, componentwise. -/
theorem contDiff_curl_apply {A : Vec3 → Vec3} (hA : ContDiff ℝ 2 A) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => curl A x i) := by
  have h2 : ∀ k, ContDiff ℝ 2 (fun y => A y k) := fun k => contDiff_pi.1 hA k
  have g1 : ContDiff ℝ 1 (fun x => pd 1 (fun z => A z 2) x) := contDiff_grad_apply (h2 2) 1
  have g2 : ContDiff ℝ 1 (fun x => pd 2 (fun z => A z 1) x) := contDiff_grad_apply (h2 1) 2
  have g3 : ContDiff ℝ 1 (fun x => pd 2 (fun z => A z 0) x) := contDiff_grad_apply (h2 0) 2
  have g4 : ContDiff ℝ 1 (fun x => pd 0 (fun z => A z 2) x) := contDiff_grad_apply (h2 2) 0
  have g5 : ContDiff ℝ 1 (fun x => pd 0 (fun z => A z 1) x) := contDiff_grad_apply (h2 1) 0
  have g6 : ContDiff ℝ 1 (fun x => pd 1 (fun z => A z 0) x) := contDiff_grad_apply (h2 0) 1
  fin_cases i <;> simp only [curl]
  · exact g1.sub g2
  · exact g3.sub g4
  · exact g5.sub g6

/-- The flux of `F` through the face `x_i = s` of the box `[a, b]`, `i`-th component. -/
noncomputable def vecFaceIntegral (F : Vec3 → Vec3) (a b : Vec3) (i : Fin 3) (s : ℝ) : ℝ :=
  ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth s y) i

/-- The flux of `F` through the (closed) boundary of the box `[a, b]`, outward normals. -/
noncomputable def boxFlux (F : Vec3 → Vec3) (a b : Vec3) : ℝ :=
  ∑ i, (vecFaceIntegral F a b i (b i) - vecFaceIntegral F a b i (a i))

/-- **The induction has no magnetic charge (Art. 403 with Art. 591), integrated over a closed
box surface:** the flux of `curl 𝔄` through the boundary of any box is zero, i.e. the six face
fluxes cancel. -/
theorem boxFlux_curl_eq_zero {A : Vec3 → Vec3} (hA : ContDiff ℝ 2 A) {a b : Vec3} (hab : a ≤ b) :
    boxFlux (curl A) a b = 0 := by
  have hfC : ∀ i, ContDiff ℝ 1 (fun x => curl A x i) := contDiff_curl_apply hA
  have hpt : ∀ x, ∑ i, fderiv ℝ (fun y => curl A y i) x (Pi.single i 1) = 0 := by
    intro x
    have h := div_curl_eq_zero hA x
    simpa [div, pd, axis] using h
  have hcont : Continuous (fun x =>
      ∑ i, fderiv ℝ (fun y => curl A y i) x (Pi.single i 1)) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hfC i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hInt : IntegrableOn (fun x =>
      ∑ i, fderiv ℝ (fun y => curl A y i) x (Pi.single i 1)) (Set.Icc a b) := by
    simp only [hpt]
    exact integrableOn_zero
  have key := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (fun i x => curl A x i) (fun i x => fderiv ℝ (fun y => curl A y i) x) ∅ Set.countable_empty
    (fun i => (hfC i).continuous.continuousOn)
    (fun x _ i => ((hfC i).differentiable (by norm_num) x).hasFDerivAt) hInt
  simp only [hpt] at key
  rw [boxFlux]
  simp only [vecFaceIntegral]
  rw [eq_comm, ← key]
  simp

end Maxwell
