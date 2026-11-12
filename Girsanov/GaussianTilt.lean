import Girsanov.Basic

/-!
# The Gaussian tilt lemma

Reweighting `𝒩(0, v)` by the one-step Girsanov weight `tiltWeight θ v` gives `𝒩(-θ v, v)`.
Hagen's single-time theorem and Farin's `girsanov_increments` both use this lemma.

## Paper plan for `gaussianReal_withDensity_exp`

1. Since `v ≠ 0`, both `𝒩(0, v)` and `𝒩(-θ v, v)` are Lebesgue measure with a Gaussian density.
2. Reweighting `volume.withDensity p` by `w` is `volume.withDensity (p * w)`.
3. So it is enough to show `p x * w x` is the shifted Gaussian density at each `x`.
   Both factors are `≥ 0`, so `ENNReal.ofReal` moves outside the product.
4. The real identity is `gaussianPDFReal_mul_exp`: complete the square,
   `-x²/(2v) - θx - θ²v/2 = -(x + θv)²/(2v)`.

| Step | Fact | Mathlib name (check with `#check`) |
|---|---|---|
| 1 | `gaussianReal μ v = volume.withDensity (gaussianPDF μ v)` for `v ≠ 0` | `gaussianReal_of_var_ne_zero` |
| 2 | `μ.withDensity (f * g) = (μ.withDensity f).withDensity g` | `withDensity_mul` |
| 3 | `ofReal (a * b) = ofReal a * ofReal b` for `0 ≤ a` | `ENNReal.ofReal_mul` |
| 3 | `0 ≤ gaussianPDFReal μ v x` | `gaussianPDFReal_nonneg` |
| 4 | formula for `gaussianPDFReal` | `gaussianPDFReal_def` |
| 4 | `exp a * exp b = exp (a + b)` | `Real.exp_add` |
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Girsanov

-- Author: Preme.

/-- Completing the square: the density of `𝒩(0, v)` times the tilt factor is the density of
`𝒩(-θ v, v)`. This holds for every `v`: if `v = 0`, both sides are `0`. -/
lemma gaussianPDFReal_mul_exp (θ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x * Real.exp (-θ * x - θ ^ 2 * (v : ℝ) / 2)
      = gaussianPDFReal (-θ * v) v x := by
  by_cases hv : v = 0
  · simp [gaussianPDFReal, hv]
  · unfold gaussianPDFReal
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring


/-- Tilting `𝒩(0, v)` by `tiltWeight θ v` gives `𝒩(-θ v, v)`. -/
lemma gaussianReal_withDensity_exp (θ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).withDensity (fun x ↦ ENNReal.ofReal (tiltWeight θ v x))
      = gaussianReal (-θ * v) v := by
  -- Follow the paper plan above: steps 1 and 2 are `rw`s, step 3 is `congr` + `funext`,
  -- step 4 is `gaussianPDFReal_mul_exp`. Measurability goals: `fun_prop`.
   rw [gaussianReal_of_var_ne_zero 0 hv, gaussianReal_of_var_ne_zero (-θ * v) hv]
   rw [← withDensity_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
   congr 1
   funext x
   simp only [Pi.mul_apply, gaussianPDF, tiltWeight]
   rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
   rw [gaussianPDFReal_mul_exp]

end Girsanov
