import Girsanov.Basic

/-!
# The Gaussian tilt lemma
The lemma states that multiplying a Gaussian probability distribution `𝒩(0, v)`
by the one-step Girsanov weight `tiltWeight θ v` produces a shifted mean & unchanged
covariance `𝒩(-θ v, v)`. This lemma is used in the single-time theorem and girsanov_increments.

## Paper plan for `gaussianReal_withDensity_exp`

1. Since `v ≠ 0`, both `𝒩(0, v)` and `𝒩(-θ v, v)` are Lebesgue measure with a Gaussian density.
2. Reweighting `volume.withDensity p` by `w` is `volume.withDensity (p * w)`.
3. So it is enough to show `p x * w x` is the shifted Gaussian density at each `x`.
   Both factors are `≥ 0`, so `ENNReal.ofReal` moves outside the product.
4. The real identity is `gaussianPDFReal_mul_exp`: complete the square,
   `-x²/(2v) - θx - θ²v/2 = -(x + θv)²/(2v)`.
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
  · simp only [gaussianPDFReal, hv, NNReal.coe_zero, mul_zero, Real.sqrt_zero, inv_zero, sub_zero,
    div_zero, Real.exp_zero, mul_one, neg_mul, zero_div, zero_mul]
  · unfold gaussianPDFReal
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring

/-- Tilting `𝒩(0, v)` by `tiltWeight θ v` gives `𝒩(-θ v, v)`. -/
lemma gaussianReal_withDensity_tiltWeight (θ : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 v).withDensity (fun x ↦ ENNReal.ofReal (tiltWeight θ v x))
      = gaussianReal (-θ * v) v := by
  by_cases hv : v = 0
  · subst hv
    simp [gaussianReal_zero_var, dirac_withDensity, tiltWeight]
  · rw [gaussianReal_of_var_ne_zero 0 hv, gaussianReal_of_var_ne_zero (-θ * v) hv]
    rw [← withDensity_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
    congr 1
    funext x
    simp only [Pi.mul_apply, gaussianPDF, tiltWeight]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    rw [gaussianPDFReal_mul_exp]

end Girsanov
