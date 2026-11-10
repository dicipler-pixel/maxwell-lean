/-
Copyright (c) 2026. Released under the MIT license (see LICENSE).
-/
import Art634Stokes

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

namespace Maxwell

open Matrix MeasureTheory
open scoped Interval

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
