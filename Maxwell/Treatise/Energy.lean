/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.MagneticStress
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Energy per unit volume, with Maxwell's split (Treatise 1873, vol. II, Arts. 630–638)

Art. 630 (p. 246): "THE energy of the system may be divided into the Potential Energy and the
Kinetic Energy." Maxwell's assignment is kept, and is the **reverse** of the later Lagrangian
bookkeeping in which `½E²` is the kinetic-like term and `B²` the potential-like term:

* electric energy is **potential**, "half the product of the electromotive force and the
  electric displacement, multiplied by the cosine of the angle which these vectors include" —
  `½ E·D` (Art. 631, p. 247). Art. 631's claim is about **totals** and is conditional: "the
  electrostatic energy of the whole field will be the same *if we suppose* that it resides in every
  part of the field where electrical force and electrical displacement occur, instead of being
  confined to the places where free electricity is found" (`Maxwell.Sources.art631`);
* magnetic (electrokinetic) energy is **kinetic**, `(1/8π) B·H` per unit volume, and "this
  energy exists in the form of some kind of motion of the matter in every portion of space"
  (Art. 636, p. 249). The "some kind of motion" clause is Maxwell's hypothesis (he points ahead
  to Art. 821); it is recorded in `Maxwell.Sources.art636`, not proved.

Where Maxwell *locates* the energy, he does so elsewhere: literally in 1865, § 74 ("On our theory
it resides in the electromagnetic field", `Maxwell.Sources.dyn1865_s74`; with § 73's "illustrative,
not as explanatory" for the mechanical words, `dyn1865_s73`), as a hypothesis in Art. 636 ("According
to our hypothesis, we assume the kinetic energy to exist wherever there is magnetic force"), and in
1873 vol. I, Art. 111 ("A dielectric medium, when thus polarized, is the seat of electrical energy",
`Maxwell.Sources.art111_energy`).

Only the *densities* are defined here. That the two volume integrals equal the old expressions
`½∑eΨ` (Art. 631) and `½∑pi` (Arts. 634–635) is stated and proved below (`art631_energyInField`,
`art631_energyInFieldDecay`, `art635_electrokineticInField`, `art635_electrokineticInFieldDecay`);
the link of `½∑pi` to the circuits (Art. 634) is still only a shape in `Maxwell.Statements`. Equal
totals do not locate the energy, and the location claims above are physical claims no integral identity can
prove.

Source: Internet Archive `electricandmagne02maxwrich` (1873, vol. II).
-/

namespace Maxwell

open Matrix

/-- The two forms of energy in Art. 630. -/
inductive EnergyForm
  | potential
  | kinetic
  deriving DecidableEq, Repr

/-- **Art. 631, p. 247:** electrostatic energy per unit volume, `½ E·D` (in quaternion language
`−½ S𝔈𝔇`). -/
noncomputable def electrostaticEnergy631 (E D : Vec3) : ℝ := (1 / 2) * (E ⬝ᵥ D)

/-- Maxwell's classification of `electrostaticEnergy631` (Arts. 630–631): potential energy. -/
def electrostaticEnergy631.form : EnergyForm := .potential

/-- **Art. 635, eq. (19), and Art. 636, p. 249:** electrokinetic energy per unit volume,
`(1/8π) B·H` (in quaternion language `−(1/8π) S𝔅ℌ`). -/
noncomputable def electrokineticEnergy636 (B H : Vec3) : ℝ := (1 / (8 * Real.pi)) * (B ⬝ᵥ H)

/-- Maxwell's classification of `electrokineticEnergy636` (Arts. 634–636, and the end of
Art. 638: "both magnetic and electromagnetic energy as kinetic energy"): kinetic energy. -/
def electrokineticEnergy636.form : EnergyForm := .kinetic

/-- **Art. 792, eqs. (22)–(23), p. 391** (isotropic medium, `4π D = K E`, `B = μ H`): the two
densities are `K E²/8π` and `μ H²/8π`. -/
theorem energy_isotropic (K μ : ℝ) (E H : Vec3) :
    electrostaticEnergy631 E ((K / fourPi) • E) = K * sq E / (8 * Real.pi) ∧
    electrokineticEnergy636 (μ • H) H = μ * sq H / (8 * Real.pi) := by
  constructor
  · simp [electrostaticEnergy631, sq, dotProduct_smul, fourPi]; field_simp; ring
  · simp [electrokineticEnergy636, sq, smul_dotProduct]; field_simp

/-! ## The integrations by parts of Arts. 631 and 635 -/

section IntegrationByParts

open MeasureTheory Filter Topology

/-- **Target (expected provable, with a sharpened hypothesis).** Treatise 1873, vol. II,
Arts. 630–631, pp. 246–247: `W = ½ ∑ eΨ`, with the quantity of electricity in an element
`(df/dx + dg/dy + dh/dz) dx dy dz`, equals `½ ∭ (Pf + Qg + Rh) dx dy dz` over all space.
Maxwell uses decay at infinity (`Ψ ~ r⁻¹`, `D ~ r⁻²`); the statement uses compact support,
which is stronger and excludes every case he treats (any system with net charge has `Ψ ~ r⁻¹`).
A `C¹` `D` also excludes the conductor surface charges of Art. 630's `½∑ eΨ`. Keep this as a
stepping stone; `Art631EnergyInFieldDecay` is the claim with his decay rates.

Equality of the two totals is all the mathematics gives, and it is all Art. 631 claims: "the
electrostatic energy of the whole field will be the same *if we suppose* that it resides…"
(`Maxwell.Sources.art631`). It does **not** locate the energy. Location is the physical claim of
1865, § 74 (`Maxwell.Sources.dyn1865_s74`), of Art. 636 as a hypothesis, and of 1873 Art. 111
("is the seat of electrical energy", `Maxwell.Sources.art111_energy`). Proved below as
`art631_energyInField`. -/
def Art631EnergyInField : Prop :=
  ∀ (Ψ : Vec3 → ℝ) (D : Vec3 → Vec3), ContDiff ℝ 1 Ψ → ContDiff ℝ 1 D →
    HasCompactSupport Ψ → HasCompactSupport D →
    (1 / 2) * ∫ x, div D x * Ψ x = ∫ x, electrostaticEnergy631 (-grad Ψ x) (D x)

/-- **Target (expected provable, with a sharpened hypothesis).** Treatise 1873, vol. II,
Arts. 634–635, eqs. (16)–(19), pp. 248–249: `T = ½ ∭ (Fu + Gv + Hw)` over the currents equals
`(1/8π) ∭ (aα + bβ + cγ)` over all space, with `𝔅 = curl 𝔄` (Art. 591) and `4πC = curl H`
(Art. 607 (E)), `C` the total current whose components are `u, v, w` (Art. 618 table; written
`C` in ASCII, not to be confused with Art. 616's `J = div 𝔄`). Compact support replaces Maxwell's decay `H ~ r⁻³` and excludes every case he treats.
Keep this as a stepping stone; `Art635ElectrokineticInFieldDecay` is the claim with his decay
rates. Again: equal totals, not a proof of where the energy is (location of the kinetic energy
is the hypothesis of Art. 636, `Maxwell.Sources.art636`, and of 1865 § 74). Proved below as
`art635_electrokineticInField`. -/
def Art635ElectrokineticInField : Prop :=
  ∀ (A H : Vec3 → Vec3), ContDiff ℝ 1 A → ContDiff ℝ 1 H →
    HasCompactSupport A → HasCompactSupport H →
    (1 / 2) * ∫ x, A x ⬝ᵥ ((1 / fourPi) • curl H x) =
      ∫ x, electrokineticEnergy636 (curl A x) (H x)

/-- Maxwell's decay in Art. 631: `Ψ` of the order `r⁻¹`, and `f, g, h` (the components of `D`)
of the order `r⁻²`, for large `r`. (`‖x‖` on `Fin 3 → ℝ` is equivalent to Euclidean `r`.) -/
def DecaysAsArt631 (Ψ : Vec3 → ℝ) (D : Vec3 → Vec3) : Prop :=
  ∃ CΨ CD : ℝ, ∀ x : Vec3, x ≠ 0 →
    |Ψ x| ≤ CΨ / ‖x‖ ∧ ∀ i, |D x i| ≤ CD / ‖x‖ ^ 2

/-- **Target (his claim).** The same equality as `Art631EnergyInField`, under Maxwell's decay
`Ψ ~ r⁻¹`, `D ~ r⁻²` (Art. 631) and integrability, rather than compact support. A `C¹` `D`
still excludes Art. 630's surface charges. Proved below as `art631_energyInFieldDecay`. -/
def Art631EnergyInFieldDecay : Prop :=
  ∀ (Ψ : Vec3 → ℝ) (D : Vec3 → Vec3), ContDiff ℝ 1 Ψ → ContDiff ℝ 1 D →
    DecaysAsArt631 Ψ D →
    Integrable (fun x => div D x * Ψ x) →
    Integrable (fun x => electrostaticEnergy631 (-grad Ψ x) (D x)) →
    (1 / 2) * ∫ x, div D x * Ψ x = ∫ x, electrostaticEnergy631 (-grad Ψ x) (D x)

/-- Maxwell prints, in Art. 635 (p. 248), that `α, β, γ` (the components of `H`) are of the
order of magnitude `r⁻³`. The companion decay `𝔄 ~ r⁻²` is ours (needed for the boundary
term, and natural for closed currents), not a rate he prints there. -/
def DecaysAsArt635 (A H : Vec3 → Vec3) : Prop :=
  ∃ CA CH : ℝ, ∀ x : Vec3, x ≠ 0 →
    (∀ i, |A x i| ≤ CA / ‖x‖ ^ 2) ∧ ∀ i, |H x i| ≤ CH / ‖x‖ ^ 3

/-- **Target (his claim, plus our decay of 𝔄).** The same equality as
`Art635ElectrokineticInField`, under Maxwell's decay `H ~ r⁻³` (Art. 635) and our `A ~ r⁻²`,
with integrability, rather than compact support. Proved below as
`art635_electrokineticInFieldDecay`. -/
def Art635ElectrokineticInFieldDecay : Prop :=
  ∀ (A H : Vec3 → Vec3), ContDiff ℝ 1 A → ContDiff ℝ 1 H →
    DecaysAsArt635 A H →
    Integrable (fun x => A x ⬝ᵥ ((1 / fourPi) • curl H x)) →
    Integrable (fun x => electrokineticEnergy636 (curl A x) (H x)) →
    (1 / 2) * ∫ x, A x ⬝ᵥ ((1 / fourPi) • curl H x) =
      ∫ x, electrokineticEnergy636 (curl A x) (H x)

/-- On a face of the cube `[-n, n]³` a point has a coordinate `±n`, so its sup norm is `≥ n`. -/
theorem le_norm_insertNth (i : Fin 3) (s : ℝ) (y : Fin 2 → ℝ) :
    |s| ≤ ‖(Fin.insertNth i s y : Vec3)‖ := by
  have := norm_le_pi_norm (Fin.insertNth i s y : Vec3) i
  simpa [Fin.insertNth_apply_same, Real.norm_eq_abs] using this

/-- **The surface term vanishes at infinity.** For a `C¹` field `F` with `|Fᵢ| ≤ C/‖x‖³` for
`‖x‖ ≥ 1` and integrable divergence, `∫ div F = 0` over all space. Proof: Mathlib's divergence
theorem on the cubes `[-n, n]³`; the six faces have area `(2n)²` and `|F| ≤ C/n³` there, so the
surface integral is at most `24C/n → 0`, while the volume integrals tend to `∫ div F`. -/
theorem integral_div_eq_zero_of_decay {F : Vec3 → Vec3} (hF : ContDiff ℝ 1 F)
    (hdecay : ∃ C : ℝ, ∀ x : Vec3, 1 ≤ ‖x‖ → ∀ i, |F x i| ≤ C / ‖x‖ ^ 3)
    (hint : Integrable (div F)) : ∫ x, div F x = 0 := by
  obtain ⟨C, hC⟩ := hdecay
  have hFi : ∀ i, ContDiff ℝ 1 (fun x => F x i) := contDiff_pi.1 hF
  set a : ℕ → Vec3 := fun n _ => -(n : ℝ) with ha
  set b : ℕ → Vec3 := fun n _ => (n : ℝ) with hb
  have hab : ∀ n, a n ≤ b n := fun n i => by simp [ha, hb]
  set bdry : ℕ → ℝ := fun n => ∑ i : Fin 3,
    ((∫ y in Set.Icc (a n ∘ i.succAbove) (b n ∘ i.succAbove), F (i.insertNth (b n i) y) i) -
      ∫ y in Set.Icc (a n ∘ i.succAbove) (b n ∘ i.succAbove), F (i.insertNth (a n i) y) i)
    with hbdry
  have hcont : Continuous (div F) := by
    unfold div pd
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hFi i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hbox : ∀ n, ∫ x in Set.Icc (a n) (b n), div F x = bdry n := by
    intro n
    exact integral_divergence_of_hasFDerivAt_off_countable' (a n) (b n) (hab n) (fun i x => F x i)
      (fun i x => fderiv ℝ (fun y => F y i) x) ∅ Set.countable_empty
      (fun i => (hFi i).continuous.continuousOn)
      (fun x _ i => ((hFi i).differentiable (by norm_num) x).hasFDerivAt)
      hcont.integrableOn_Icc
  -- each face integral is at most `C / n³ · (2n)²`
  have hface : ∀ n : ℕ, 1 ≤ n → ∀ (i : Fin 3) (s : ℝ), |s| = n →
      |∫ y in Set.Icc (a n ∘ i.succAbove) (b n ∘ i.succAbove), F (i.insertNth s y) i| ≤
        C / (n : ℝ) ^ 3 * (2 * n) ^ 2 := by
    intro n hn i s hs
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hle : a n ∘ i.succAbove ≤ b n ∘ i.succAbove := fun j => hab n (i.succAbove j)
    have hvol : volume.real (Set.Icc (a n ∘ i.succAbove) (b n ∘ i.succAbove)) = (2 * n) ^ 2 := by
      rw [measureReal_def, Real.volume_Icc_pi_toReal hle]
      simp [ha, hb]; ring
    rw [← hvol, ← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (by
      rw [Real.volume_Icc_pi]; exact ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)) ?_
    intro y _
    have hz := le_norm_insertNth i s y
    rw [hs] at hz
    have h1 := hC _ (hn1.trans hz) i
    have hC0 : 0 ≤ C := by
      have : 0 ≤ C / ‖(Fin.insertNth i s y : Vec3)‖ ^ 3 := (abs_nonneg _).trans h1
      have hp : 0 < ‖(Fin.insertNth i s y : Vec3)‖ ^ 3 := pow_pos (by linarith) 3
      by_contra hneg
      have : C / ‖(Fin.insertNth i s y : Vec3)‖ ^ 3 < 0 := div_neg_of_neg_of_pos (by linarith) hp
      linarith
    rw [Real.norm_eq_abs]
    refine h1.trans (div_le_div_of_nonneg_left hC0 (pow_pos (by linarith) 3) ?_)
    exact pow_le_pow_left₀ (by positivity) hz 3
  have hbd : ∀ n : ℕ, 1 ≤ n → ‖bdry n‖ ≤ 24 * C / n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : ∀ i : Fin 3, |b n i| = n := fun i => by simp [hb]
    have hm : ∀ i : Fin 3, |a n i| = n := fun i => by simp [ha]
    have e : C / (n : ℝ) ^ 3 * (2 * n) ^ 2 = 4 * C / n := by
      field_simp; ring
    have key := fun (i : Fin 3) (s : ℝ) (hs : |s| = (n : ℝ)) => abs_le.1 (hface n hn i s hs)
    rw [Real.norm_eq_abs, abs_le]
    simp only [hbdry, Fin.sum_univ_three]
    obtain ⟨h1, h2⟩ := key 0 _ (hp 0); obtain ⟨h3, h4⟩ := key 0 _ (hm 0)
    obtain ⟨h5, h6⟩ := key 1 _ (hp 1); obtain ⟨h7, h8⟩ := key 1 _ (hm 1)
    obtain ⟨h9, h10⟩ := key 2 _ (hp 2); obtain ⟨h11, h12⟩ := key 2 _ (hm 2)
    rw [e] at *
    have h24 : 24 * C / (n : ℝ) = 6 * (4 * C / n) := by ring
    rw [h24]
    constructor <;> linarith
  have hlim : Tendsto bdry atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (24 * C))
    filter_upwards [eventually_ge_atTop 1] with n hn using hbd n hn
  have hmono : Monotone fun n => Set.Icc (a n) (b n) := by
    intro m n hmn
    apply Set.Icc_subset_Icc <;> intro i <;> simp [ha, hb] <;> exact_mod_cast hmn
  have hunion : (⋃ n, Set.Icc (a n) (b n)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    refine ⟨n, fun i => ?_, fun i => ?_⟩ <;>
      have := (abs_le.1 ((Real.norm_eq_abs _).symm.trans_le ((norm_le_pi_norm x i).trans hn)))
    · simp [ha]; linarith [this.1]
    · simp [hb]; linarith [this.2]
  have hT := tendsto_setIntegral_of_monotone (μ := volume) (f := div F)
    (fun n => measurableSet_Icc) hmono (by rw [hunion]; exact hint.integrableOn)
  rw [hunion, Measure.restrict_univ] at hT
  simp_rw [hbox] at hT
  exact tendsto_nhds_unique hT hlim

/-- A function vanishing wherever a compactly supported `g` vanishes has compact support. -/
theorem hasCompactSupport_of_vanish {E F : Type*} [Zero E] [Zero F] {f : Vec3 → F} {g : Vec3 → E}
    (hg : HasCompactSupport g) (h : ∀ x, g x = 0 → f x = 0) : HasCompactSupport f :=
  hg.mono fun x hx hgx => hx (h x hgx)

/-- A continuous compactly supported function is `O(‖x‖⁻ᵏ)` for every `k`, on `x ≠ 0`. -/
theorem bound_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E] {f : Vec3 → E}
    (hf : Continuous f) (hs : HasCompactSupport f) (k : ℕ) :
    ∃ C : ℝ, ∀ x : Vec3, x ≠ 0 → ‖f x‖ ≤ C / ‖x‖ ^ k := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hs
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec3)).1 hs.isCompact.isBounded
  refine ⟨max M 0 * max R 0 ^ k, fun x hx => ?_⟩
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  by_cases hxR : ‖x‖ ≤ max R 0
  · rw [le_div_iff₀ (pow_pos hx0 k)]
    exact mul_le_mul ((hM x).trans (le_max_left _ _)) (pow_le_pow_left₀ hx0.le hxR k)
      (by positivity) (le_max_right _ _)
  · have : x ∉ tsupport f := fun h => hxR <| by
      have := hR h; rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    rw [image_eq_zero_of_notMem_tsupport this, norm_zero]
    positivity

/-- **Art. 631, with Maxwell's decay** (`Ψ ~ r⁻¹`, `D ~ r⁻²`). From
`div (Ψ D) = ∇Ψ · D + Ψ div D` (`div_smul`) and `integral_div_eq_zero_of_decay` (`|Ψ D| ~ r⁻³`).
No constitutive relation between `D` and `E = −∇Ψ` is used. -/
theorem art631_energyInFieldDecay : Art631EnergyInFieldDecay := by
  intro Ψ D hΨ hD ⟨CΨ, CD, hdec⟩ hint1 hint2
  have hΨd : ∀ x, DifferentiableAt ℝ Ψ x := fun x => hΨ.differentiable (by norm_num) x
  have hDd : ∀ x i, DifferentiableAt ℝ (fun y => D y i) x := fun x i =>
    (contDiff_pi.1 hD i).differentiable (by norm_num) x
  have hgD : (fun x => grad Ψ x ⬝ᵥ D x) =
      fun x => (-2) * electrostaticEnergy631 (-grad Ψ x) (D x) := by
    funext x; simp [electrostaticEnergy631, neg_dotProduct]
  have hint3 : Integrable (fun x => grad Ψ x ⬝ᵥ D x) := by rw [hgD]; exact hint2.const_mul _
  have hdivF : div (fun y => Ψ y • D y) = fun x => grad Ψ x ⬝ᵥ D x + div D x * Ψ x := by
    funext x; rw [div_smul (hΨd x) (hDd x), mul_comm (Ψ x)]
  have h0 := integral_div_eq_zero_of_decay (F := fun y => Ψ y • D y) (hΨ.smul hD)
    ⟨CΨ * CD, fun x hx i => by
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
      obtain ⟨h1, h2⟩ := hdec x hx0
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      calc |Ψ x| * |D x i| ≤ CΨ / ‖x‖ * (CD / ‖x‖ ^ 2) :=
            mul_le_mul h1 (h2 i) (abs_nonneg _) ((abs_nonneg _).trans h1)
        _ = CΨ * CD / ‖x‖ ^ 3 := by ring⟩
    (by rw [hdivF]; exact hint3.add hint1)
  rw [hdivF, integral_add hint3 hint1] at h0
  have hE : (fun x => electrostaticEnergy631 (-grad Ψ x) (D x)) =
      fun x => (-1 / 2) * (grad Ψ x ⬝ᵥ D x) := by
    funext x; simp [electrostaticEnergy631, neg_dotProduct]; ring
  rw [hE, integral_const_mul]
  linarith

/-- **Art. 631, compact support** (a special case of `art631_energyInFieldDecay`). -/
theorem art631_energyInField : Art631EnergyInField := by
  intro Ψ D hΨ hD hsΨ hsD
  have hcΨ := hΨ.continuous
  have hcD := hD.continuous
  refine art631_energyInFieldDecay Ψ D hΨ hD ?_ ?_ ?_
  · obtain ⟨C1, h1⟩ := bound_of_hasCompactSupport hcΨ hsΨ 1
    obtain ⟨C2, h2⟩ := bound_of_hasCompactSupport hcD hsD 2
    refine ⟨C1, C2, fun x hx => ⟨by simpa using h1 x hx, fun i => ?_⟩⟩
    have := (norm_le_pi_norm (D x) i).trans (h2 x hx)
    rwa [Real.norm_eq_abs] at this
  · exact ((continuous_div hD).mul hcΨ).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish hsΨ fun x hx => by simp [hx])
  · exact (continuous_const.mul ((continuous_grad hΨ).neg.dotProduct hcD)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish hsD fun x hx => by simp [hx])

/-- **Art. 635, with Maxwell's decay `H ~ r⁻³` and our `𝔄 ~ r⁻²`.** From
`div (𝔄 × H) = H · curl 𝔄 − 𝔄 · curl H` (`div_cross`) and `integral_div_eq_zero_of_decay`
(`|𝔄 × H| ~ r⁻⁵`). No relation `𝔅 = μH` and no current is assumed: `C = (1/4π) curl H` is
written into the statement. -/
theorem art635_electrokineticInFieldDecay : Art635ElectrokineticInFieldDecay := by
  intro A H hA hH ⟨CA, CH, hdec⟩ hint1 hint2
  have hAd : ∀ x i, DifferentiableAt ℝ (fun y => A y i) x := fun x i =>
    (contDiff_pi.1 hA i).differentiable (by norm_num) x
  have hHd : ∀ x i, DifferentiableAt ℝ (fun y => H y i) x := fun x i =>
    (contDiff_pi.1 hH i).differentiable (by norm_num) x
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have e1 : (fun x => A x ⬝ᵥ curl H x) = fun x => fourPi * (A x ⬝ᵥ ((1 / fourPi) • curl H x)) := by
    funext x; rw [dotProduct_smul, smul_eq_mul]; field_simp
  have e2 : (fun x => H x ⬝ᵥ curl A x) =
      fun x => (8 * Real.pi) * electrokineticEnergy636 (curl A x) (H x) := by
    funext x; simp only [electrokineticEnergy636]; rw [dotProduct_comm]; field_simp
  have i1 : Integrable (fun x => A x ⬝ᵥ curl H x) := by rw [e1]; exact hint1.const_mul _
  have i2 : Integrable (fun x => H x ⬝ᵥ curl A x) := by rw [e2]; exact hint2.const_mul _
  have hdivF : div (fun y => crossProduct (A y) (H y)) =
      fun x => H x ⬝ᵥ curl A x - A x ⬝ᵥ curl H x := by
    funext x; exact div_cross (hAd x) (hHd x)
  have hcross : ContDiff ℝ 1 (fun y => crossProduct (A y) (H y)) := by
    refine contDiff_pi.2 fun i => ?_
    have a := contDiff_pi.1 hA; have h := contDiff_pi.1 hH
    fin_cases i <;> simp only [cross_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] <;> fun_prop
  have h0 := integral_div_eq_zero_of_decay hcross
    ⟨2 * (CA * CH), fun x hx i => by
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
      have hr : 0 < ‖x‖ := norm_pos_iff.2 hx0
      obtain ⟨h1, h2⟩ := hdec x hx0
      have hCA : 0 ≤ CA := by
        have := (abs_nonneg _).trans (h1 0)
        by_contra hn; exact absurd this (not_le.2 (div_neg_of_neg_of_pos (by linarith) (by positivity)))
      have hCH : 0 ≤ CH := by
        have := (abs_nonneg _).trans (h2 0)
        by_contra hn; exact absurd this (not_le.2 (div_neg_of_neg_of_pos (by linarith) (by positivity)))
      refine (abs_cross_apply_le h1 h2 i).trans ?_
      have : CA / ‖x‖ ^ 2 * (CH / ‖x‖ ^ 3) = CA * CH / ‖x‖ ^ 5 := by ring
      rw [this, mul_div_assoc']
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hr 3)
        (pow_le_pow_right₀ hx (by norm_num : 3 ≤ 5))⟩
    (by rw [hdivF]; exact i2.sub i1)
  rw [hdivF, integral_sub i2 i1, sub_eq_zero] at h0
  have l : (fun x => A x ⬝ᵥ ((1 / fourPi) • curl H x)) =
      fun x => (1 / fourPi) * (A x ⬝ᵥ curl H x) := by
    funext x; rw [dotProduct_smul, smul_eq_mul]
  have r : (fun x => electrokineticEnergy636 (curl A x) (H x)) =
      fun x => (1 / (8 * Real.pi)) * (H x ⬝ᵥ curl A x) := by
    funext x; simp only [electrokineticEnergy636]; rw [dotProduct_comm]
  rw [l, r, integral_const_mul, integral_const_mul, h0]
  simp only [fourPi]; field_simp; ring

/-- **Art. 635, compact support** (a special case of `art635_electrokineticInFieldDecay`). -/
theorem art635_electrokineticInField : Art635ElectrokineticInField := by
  intro A H hA hH hsA hsH
  refine art635_electrokineticInFieldDecay A H hA hH ?_ ?_ ?_
  · obtain ⟨C1, h1⟩ := bound_of_hasCompactSupport hA.continuous hsA 2
    obtain ⟨C2, h2⟩ := bound_of_hasCompactSupport hH.continuous hsH 3
    refine ⟨C1, C2, fun x hx => ⟨fun i => ?_, fun i => ?_⟩⟩
    · have := (norm_le_pi_norm (A x) i).trans (h1 x hx); rwa [Real.norm_eq_abs] at this
    · have := (norm_le_pi_norm (H x) i).trans (h2 x hx); rwa [Real.norm_eq_abs] at this
  · have hc : Continuous (fun x => A x ⬝ᵥ ((1 / fourPi) • curl H x)) :=
      have h2 : Continuous (fun x => (1 / fourPi) • curl H x) :=
        (continuous_curl hH).const_smul (1 / fourPi)
      hA.continuous.dotProduct h2
    exact hc.integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish hsA fun x hx => by rw [hx, zero_dotProduct])
  · have hc : Continuous (fun x => electrokineticEnergy636 (curl A x) (H x)) := by
      unfold electrokineticEnergy636
      exact continuous_const.mul ((continuous_curl hA).dotProduct hH.continuous)
    exact hc.integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish hsH fun x hx => by
        simp only [electrokineticEnergy636, hx, dotProduct_zero, mul_zero])

end IntegrationByParts

end Maxwell
