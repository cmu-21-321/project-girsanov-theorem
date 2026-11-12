import Girsanov.Basic
import Girsanov.DensityTransfer
import Girsanov.GaussianTilt
import Girsanov.SingleTime

/-!
# Girsanov for finitely many observation times

Under `P`, the increments `ΔW k` are independent with `ΔW k ∼ 𝒩(0, Δtₖ)`.
Under the Girsanov measure `Q = girsanovMeasure P g θ ΔW`, the shifted increments
`ΔW k + θ k * Δtₖ` have the same law, `incrementLaw g = ⨂ₖ 𝒩(0, Δtₖ)`.

## Step · Fact · Mathlib name

* Independence. `iIndepFun f μ ↔ μ.map (fun ω i ↦ f i ω) = Measure.pi fun i ↦ μ.map (f i)`
  (conditions: `IsProbabilityMeasure μ` and `AEMeasurable` components):
  `iIndepFun_iff_map_fun_eq_pi_map`.
* Independence. The coordinates are independent under `Measure.pi`: `iIndepFun_pi`.
* Shift. `(Measure.pi μ).map (fun x i ↦ f i (x i)) = Measure.pi fun i ↦ (μ i).map (f i)`:
  `Measure.pi_map_pi`.
* Shift. `(gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v`:
  `gaussianReal_map_add_const`.
* Probability. `Measure.pi` of probability measures is a probability measure:
  instance `Measure.pi.instIsProbabilityMeasure`. Lean finds this instance automatically
  for `incrementLaw`, because `incrementLaw` is an `abbrev`.

`iIndepFun` has only two arguments, the family and the measure: `iIndepFun ΔW P`.
In this Mathlib version, `iIndepFun` has no explicit `MeasurableSpace` argument.

## Main results

* `girsanov_gaussian_pi`: the self-contained version. It uses only Mathlib notions
  (`Measure.withDensity`, `Measure.pi`, `gaussianReal`), any finite index set and any
  variances `vₖ ≥ 0`. It does not use `TimeGrid` or our other definitions, so it can be
  used outside this project.
* `girsanov_increments`: the version for a time grid. It is `girsanov_gaussian_pi` with
  `vₖ = Δtₖ`. Lean accepts it directly, because `girsanovMeasure` unfolds to the
  `withDensity` in `girsanov_gaussian_pi`.

## Plan for `girsanov_gaussian_pi`

1. The density is a function of the vector `Y ω = (X k ω)ₖ`: it is the product of the
   `tiltWeight`s at `Y ω` (`prod_tiltWeight`). The shifted vector is also a function of `Y`.
2. `Measure.map_map` and `map_withDensity_comp` move the density to the law of `Y`.
3. By independence (`iIndepFun_iff_map_fun_eq_pi_map`), the law of `Y` is
   `Measure.pi fun k ↦ 𝒩(0, vₖ)`.
4. `pi_withDensity` splits the product density across the product. Tilt each coordinate
   with `gaussianReal_withDensity_tiltWeight`. Then coordinate `k` is `𝒩(-θₖ vₖ, vₖ)`.
5. Shift every coordinate by `θₖ vₖ` with `Measure.pi_map_pi` and
   `gaussianReal_map_add_const`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Girsanov

variable {n : ℕ}

/-- The increment law with the Girsanov density is a product of tilted Gaussians,
one for each step. -/
theorem incrementLaw_withDensity (g : TimeGrid n) (θ : Fin n → ℝ) :
    (incrementLaw g).withDensity (fun x ↦ ENNReal.ofReal (canonicalDensity g θ x))
      = Measure.pi fun k ↦ (gaussianReal 0 (g.Δt k)).withDensity
          fun y ↦ ENNReal.ofReal (tiltWeight (θ k) (g.Δt k) y) := by
  -- Move `ofReal` inside the product (each factor is positive), then split the product.
  have h : (fun x ↦ ENNReal.ofReal (canonicalDensity g θ x))
      = fun x ↦ ∏ k, ENNReal.ofReal (tiltWeight (θ k) (g.Δt k) (x k)) :=
    funext fun x ↦ ENNReal.ofReal_prod_of_nonneg fun k _ ↦ (tiltWeight_pos _ _ _).le
  rw [h]
  exact pi_withDensity (μ := fun k ↦ gaussianReal 0 (g.Δt k))
    (f := fun k y ↦ ENNReal.ofReal (tiltWeight (θ k) (g.Δt k) y))
    (fun _ ↦ by fun_prop) fun _ _ ↦ ENNReal.ofReal_ne_top

/-! ### A self-contained version

The theorem `girsanov_gaussian_pi` below uses only Mathlib notions: a finite index set `ι`,
variances `v : ι → ℝ≥0`, `Measure.withDensity` and `Measure.pi`. It does not use
`TimeGrid`, `girsanovMeasure` or `incrementLaw`. The variances may also be `0`. -/

section General

variable {ι : Type*} [Fintype ι]

/-- A product of tilt weights is the exponential of a sum:
`∏ₖ exp(-θₖ xₖ - θₖ² vₖ / 2) = exp(-∑ₖ θₖ xₖ - ½ ∑ₖ θₖ² vₖ)`. -/
lemma prod_tiltWeight (θ : ι → ℝ) (v : ι → ℝ≥0) (x : ι → ℝ) :
    ∏ k, tiltWeight (θ k) (v k) (x k) =
      Real.exp (-(∑ k, θ k * x k) - (1 / 2) * ∑ k, θ k ^ 2 * (v k : ℝ)) := by
  unfold tiltWeight
  -- A product of exponentials is the exponential of a sum.
  rw [← Real.exp_sum]
  -- Compare the two exponents term by term.
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The Gaussian tilt for every variance. If `v = 0`, both sides are the point mass at `0`.
Otherwise this is `gaussianReal_withDensity_exp`. -/
lemma gaussianReal_withDensity_tiltWeight (θ : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 v).withDensity (fun x ↦ ENNReal.ofReal (tiltWeight θ v x))
      = gaussianReal (-θ * v) v := by
  by_cases hv : v = 0
  · subst hv
    simp [gaussianReal_zero_var, dirac_withDensity, tiltWeight]
  · exact gaussianReal_withDensity_exp θ hv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ι → Ω → ℝ}

/-- **Girsanov for independent Gaussians.** Let `X k ∼ 𝒩(0, vₖ)` be independent under `P`.
Reweight `P` by `exp(-∑ₖ θₖ Xₖ - ½ ∑ₖ θₖ² vₖ)`. Under the new measure, the shifted
variables `X k + θₖ vₖ` are independent with law `𝒩(0, vₖ)`. -/
theorem girsanov_gaussian_pi (v : ι → ℝ≥0) (hmeas : ∀ k, Measurable (X k))
    (hind : iIndepFun X P) (hlaw : ∀ k, P.map (X k) = gaussianReal 0 (v k)) (θ : ι → ℝ) :
    (P.withDensity fun ω ↦ ENNReal.ofReal
        (Real.exp (-(∑ k, θ k * X k ω) - (1 / 2) * ∑ k, θ k ^ 2 * (v k : ℝ)))).map
        (fun ω k ↦ X k ω + θ k * (v k : ℝ))
      = Measure.pi fun k ↦ gaussianReal 0 (v k) := by
  -- Step 0: The vector `Y ω = (X k ω)ₖ`. The density and the shifted vector are functions
  -- of `Y`.
  set Y : Ω → ι → ℝ := fun ω k ↦ X k ω
  have hY : Measurable Y := measurable_pi_iff.2 hmeas
  simp_rw [← prod_tiltWeight,
    ENNReal.ofReal_prod_of_nonneg fun k _ ↦ (tiltWeight_pos _ _ _).le]
  change (P.withDensity
      ((fun x ↦ ∏ k, ENNReal.ofReal (tiltWeight (θ k) (v k) (x k))) ∘ Y)).map
    ((fun x k ↦ x k + θ k * (v k : ℝ)) ∘ Y) = _
  -- Step 1: Map by `Y` first, then shift. The density moves to the law of `Y`
  -- (`map_withDensity_comp`).
  rw [← Measure.map_map (by fun_prop) hY, map_withDensity_comp P hY (by fun_prop)]
  -- Step 2: By independence, the law of `Y` under `P` is the Gaussian product measure.
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun k ↦ (hmeas k).aemeasurable).1 hind]
  simp only [hlaw]
  -- Step 3: Split the product density across the product, and tilt each coordinate.
  rw [pi_withDensity (fun _ ↦ by fun_prop) fun _ _ ↦ ENNReal.ofReal_ne_top]
  simp only [gaussianReal_withDensity_tiltWeight]
  -- Step 4: Shift each coordinate by `θₖ vₖ`. This recentres `𝒩(-θₖ vₖ, vₖ)` at `0`.
  have hshift : ∀ k, (gaussianReal (-θ k * v k) (v k)).map (· + θ k * (v k : ℝ))
      = gaussianReal 0 (v k) := fun k ↦ by
    rw [gaussianReal_map_add_const, neg_mul, neg_add_cancel]
  have : ∀ k, SigmaFinite ((gaussianReal (-θ k * v k) (v k)).map (· + θ k * (v k : ℝ))) :=
    fun k ↦ by rw [hshift k]; infer_instance
  rw [Measure.pi_map_pi (f := fun k y ↦ y + θ k * (v k : ℝ)) fun k ↦ by fun_prop]
  simp only [hshift]

end General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (g : TimeGrid n) {ΔW : Fin n → Ω → ℝ}

/-- Independent Gaussian increments have the product law `incrementLaw g`. (Week 3) -/
theorem map_increments_eq_pi (hmeas : ∀ k, Measurable (ΔW k)) (hind : iIndepFun ΔW P)
    (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k)) :
    P.map (fun ω k ↦ ΔW k ω) = incrementLaw g := by
  -- The increments are independent. Thus their joint law is the product of the laws
  -- of the coordinates.
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun k ↦ (hmeas k).aemeasurable).1 hind]
  -- The law of each coordinate is the Gaussian `𝒩(0, Δtₖ)`.
  simp only [hlaw]

/-- **Girsanov for the increments.** Under `Q`, the shifted increments
`ΔW k + θ k * Δtₖ` are independent with law `𝒩(0, Δtₖ)`. (Week 4)

This is `girsanov_gaussian_pi` with the variances `Δtₖ` of the time grid. -/
theorem girsanov_increments (hmeas : ∀ k, Measurable (ΔW k)) (hind : iIndepFun ΔW P)
    (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k)) (θ : Fin n → ℝ) :
    (girsanovMeasure P g θ ΔW).map (fun ω k ↦ ΔW k ω + θ k * (g.Δt k : ℝ))
      = incrementLaw g :=
  girsanov_gaussian_pi g.Δt hmeas hind hlaw θ

/-- **Example (n = 1).** With one step, `girsanov_increments` gives the single-time
theorem for `W = ΔW 0` and `T = Δt₀`: the statement below has the same form as
`girsanov_single_time`. A single variable is always independent, so no independence
hypothesis is needed. (Week 4) -/
example (g : TimeGrid 1) {ΔW : Fin 1 → Ω → ℝ} (hmeas : ∀ k, Measurable (ΔW k))
    (hlaw : P.map (ΔW 0) = gaussianReal 0 (g.Δt 0)) (θ : ℝ) :
    (P.withDensity fun ω ↦ ENNReal.ofReal
        (Real.exp (-θ * ΔW 0 ω - θ ^ 2 * (g.Δt 0 : ℝ) / 2))).map
        (fun ω ↦ ΔW 0 ω + θ * (g.Δt 0 : ℝ))
      = gaussianReal 0 (g.Δt 0) := by
  -- Apply `girsanov_increments` with the constant drift `θ`.
  have h := girsanov_increments g hmeas (iIndepFun.of_subsingleton)
    (fun k ↦ by rw [Subsingleton.elim k 0]; exact hlaw) (fun _ ↦ θ)
  -- Look only at coordinate `0`: map both sides by `Function.eval 0`.
  have h0 := congrArg (fun μ ↦ μ.map (Function.eval (0 : Fin 1))) h
  rw [Measure.map_map (measurable_pi_apply 0) (by fun_prop),
    (measurePreserving_eval (fun k ↦ gaussianReal 0 (g.Δt k)) 0).map_eq] at h0
  -- For `n = 1`, the sums in the Girsanov density have one term.
  convert h0 using 3
  · rfl
  · unfold girsanovMeasure
    congr 1
    funext ω
    simp only [girsanovDensity, Fin.sum_univ_one]
    ring_nf

end Girsanov
