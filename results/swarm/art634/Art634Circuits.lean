/-
Copyright (c) 2026. Released under the MIT license (see LICENSE).
-/
import Art634Stokes

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

namespace Maxwell

open Matrix MeasureTheory
open scoped Interval

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

end Maxwell
