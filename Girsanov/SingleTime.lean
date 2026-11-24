import Girsanov.Basic
import Girsanov.GaussianTilt

/-!
# Girsanov at a single time

Under `P` let `W ∼ 𝒩(0, T)`. Reweighting `P` by `exp(-θ W - θ² T / 2)` gives a measure `Q`
under which `W + θ T ∼ 𝒩(0, T)`. This file also has the change-of-variables lemma
`map_withDensity_comp` used in `girsanov_increments`, and the fact that the Girsanov
measure is a probability measure.

## Step · Fact · Mathlib name

* Pushforward. `μ.map f s = μ (f ⁻¹' s)` for measurable `f` and `s`: `Measure.map_apply`.
* Pushforward. `∫⁻ a in s, g a ∂(μ.map f) = ∫⁻ x in f ⁻¹' s, g (f x) ∂μ`: `setLIntegral_map`.
* Density. `μ.withDensity f s = ∫⁻ a in s, f a ∂μ` for measurable `s`: `withDensity_apply`.
* Mass. `μ.withDensity f univ = ∫⁻ a, f a ∂μ`: `withDensity_apply _ MeasurableSet.univ`,
  then `Measure.restrict_univ`.
* Tilt. `𝒩(0, T).withDensity (exp(-θ x - θ² T / 2)) = 𝒩(-θ T, T)`:
  `gaussianReal_withDensity_tiltWeight` (Girsanov/GaussianTilt.lean).
* Shift. `(gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v`:
  `gaussianReal_map_add_const`.

## Plan for `map_withDensity_comp`

`ext s hs`, then `rw [Measure.map_apply hX hs, withDensity_apply _ (hX hs),
withDensity_apply _ hs, setLIntegral_map hs hf hX]`, and the two sides agree.

## Plan for `girsanov_single_time`

1. `map_withDensity_comp` with `f x = ofReal (exp(-θ x - θ² T / 2))` turns the law of `W`
   under `Q` into `𝒩(0, T).withDensity f`.
2. The Gaussian tilt makes this `𝒩(-θ T, T)`.
3. `Measure.map_map` and `gaussianReal_map_add_const` shift it to `𝒩(0, T)`.

## Plan for `isProbabilityMeasure_girsanovMeasure`

The mgf route. Write the density as `exp(∑ₖ Xₖ) · exp(-c)` with `Xₖ = -θₖ ΔWₖ` and
`c = ½ ∑ₖ θₖ² Δtₖ`. The total mass is `E_P[exp(∑ₖ Xₖ)] · exp(-c)` (`withDensity_apply`,
`ofReal_integral_eq_lintegral_ofReal`). The `Xₖ` are independent (`iIndepFun.comp`), so
the expectation is `∏ₖ mgf Xₖ 1` (`iIndepFun.mgf_sum`), and each factor is the Gaussian mgf
`exp(θₖ² Δtₖ / 2)` (`mgf_const_mul`, `mgf_gaussianReal`). The product is `exp(c)`, which
cancels `exp(-c)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Girsanov

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Reweighting by a density that factors through `X` and then pushing forward along `X`
is the same as pushing forward first and reweighting the law of `X`. -/
theorem map_withDensity_comp (P : Measure Ω) {X : Ω → α} (hX : Measurable X)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (P.withDensity (f ∘ X)).map X = (P.map X).withDensity f := by
  -- Two measures are equal if they agree on every measurable set `s`.
  ext s hs
  -- Both sides are integrals of the density: over `X ⁻¹' s` against `P`, and over `s`
  -- against the law of `X`. Change of variables makes them equal.
  rw [Measure.map_apply hX hs, withDensity_apply _ (hX hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hX, Function.comp_def]

/-- **Girsanov at a single time.** If `W ∼ 𝒩(0, T)` under `P`, then under
`Q = P.withDensity (exp(-θ W - θ² T / 2))` the shifted variable `W + θ T` is `𝒩(0, T)`. -/
theorem girsanov_single_time (P : Measure Ω) {W : Ω → ℝ} (hW : Measurable W) (T : ℝ≥0)
    (hlaw : P.map W = gaussianReal 0 T) (θ : ℝ) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * W ω - θ ^ 2 * T / 2))).map
        (fun ω ↦ W ω + θ * T)
      = gaussianReal 0 T := by
  -- The density is `f ∘ W` with `f = ofReal ∘ tiltWeight θ T`, and the shifted variable is
  -- `(· + θ T) ∘ W`. Both are functions of `W`.
  change (P.withDensity ((fun x ↦ ENNReal.ofReal (tiltWeight θ T x)) ∘ W)).map
      ((· + θ * T) ∘ W) = _
  -- (a) Map by `W` first, then shift. (b) Move the density to the law of `W`, which is
  -- `𝒩(0, T)`. (c) The Gaussian tilt gives `𝒩(-θ T, T)`. (d) The shift recentres it at `0`.
  rw [← Measure.map_map (by fun_prop) hW, map_withDensity_comp P hW (by fun_prop), hlaw,
    gaussianReal_withDensity_tiltWeight, gaussianReal_map_add_const, neg_mul, neg_add_cancel]

/-- **Example (θ = 0).** With no drift the density is `1` and the shift is `0`, so the left
side of `girsanov_single_time` is the law of `W` under `P`. Thus for `θ = 0` the theorem says
`P.map W = gaussianReal 0 T`, which is exactly the hypothesis `hlaw`. -/
example (P : Measure Ω) (W : Ω → ℝ) (T : ℝ≥0) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-0 * W ω - 0 ^ 2 * T / 2))).map
        (fun ω ↦ W ω + 0 * T)
      = P.map W := by
  simp

/-- For independent Gaussian increments, the Girsanov measure is a probability measure. -/
theorem isProbabilityMeasure_girsanovMeasure {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (g : TimeGrid n) {ΔW : Fin n → Ω → ℝ} (hmeas : ∀ k, Measurable (ΔW k))
    (hind : iIndepFun ΔW P) (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k))
    (θ : Fin n → ℝ) :
    IsProbabilityMeasure (girsanovMeasure P g θ ΔW) := by
  -- The exponent splits as `∑ₖ Xₖ - c`, with `Xₖ = -θₖ ΔWₖ` and `c = ½ ∑ₖ θₖ² Δtₖ`.
  set X : Fin n → Ω → ℝ := fun k ω ↦ -θ k * ΔW k ω with hX
  set c : ℝ := (1 / 2) * ∑ k, θ k ^ 2 * (g.Δt k : ℝ) with hc
  have hXmeas : ∀ k, Measurable (X k) := fun k ↦ (hmeas k).const_mul _
  have hXind : iIndepFun X P := hind.comp (fun k x ↦ -θ k * x) fun k ↦ by fun_prop
  have hZ : girsanovDensity g θ ΔW = fun ω ↦ Real.exp (1 * (∑ k, X k) ω) * Real.exp (-c) := by
    funext ω
    rw [girsanovDensity, ← Real.exp_add, Finset.sum_apply, ← Finset.sum_neg_distrib]
    simp only [hX, hc, one_mul, neg_mul, sub_eq_add_neg]
  -- `exp(∑ₖ Xₖ)` is integrable: each `exp(Xₖ)` is, since `ΔWₖ` is Gaussian.
  have hint : Integrable (fun ω ↦ Real.exp (1 * (∑ k, X k) ω)) P := by
    refine hXind.integrable_exp_mul_sum hXmeas fun k _ ↦ ?_
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := g.Δt k) (-θ k)
    rw [← hlaw k] at h
    simpa [hX, Function.comp_def, mul_assoc] using h.comp_measurable (hmeas k)
  -- By independence, `E[exp(∑ₖ Xₖ)]` is the product of the Gaussian mgfs `exp(θₖ² Δtₖ / 2)`.
  have hmgf : mgf (∑ k, X k) P 1 = Real.exp c := by
    rw [hXind.mgf_sum hXmeas, hc, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [hX, mgf_const_mul, mgf_gaussianReal ⟨(hmeas k).aemeasurable, hlaw k⟩]
    congr 1
    ring
  -- The total mass of `Q` is `E[exp(∑ₖ Xₖ)] · exp(-c) = exp(c) · exp(-c) = 1`.
  constructor
  rw [girsanovMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (by rw [hZ]; exact hint.mul_const _)
      (Filter.Eventually.of_forall fun ω ↦ (girsanovDensity_pos g θ ΔW ω).le)]
  rw [hZ, integral_mul_const, ← mgf, hmgf, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    ENNReal.ofReal_one]

end Girsanov
